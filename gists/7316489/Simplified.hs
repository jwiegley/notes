{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module Simplified where

import Data.List (groupBy, sort, nub)
import Data.Maybe
import Data.Text (Text)
import Data.Text.Encoding (encodeUtf8)
import Database.Esqueleto hiding (groupBy)
import FP.Merchant.Database
import FP.Merchant.Model
import FP.Merchant.State
import Text.Show.Pretty

data Freq = Monthly | Annual deriving Show
type SKU = Text

data Probono      = Probono AccountId deriving Show
data Academic     = Academic AccountId deriving Show
data Trial        = Trial AccountId UTCTime deriving Show -- expiration
data Personal     = Personal AccountId Freq UTCTime deriving Show -- next charge
data Professional = Professional AccountId SKU UTCTime [Maybe Userid]
    deriving Show

checkUniqueness :: (Monad m, Applicative m, Functor m, Ord a, Eq a, Show a)
                => String -> [a] -> m ()
checkUniqueness label xs =
    void $ for (groupBy (==) (sort xs)) $ \xs' ->
        case length xs' of
            1 -> return ()
            _ -> error $ label ++ ": " ++ ppShow xs

findProbono :: MonadMerchant m => SqlPersistT m [Probono]
findProbono = do
    xs <- select $ from $ \acct -> do
        where_ ( acct^.AccountType ==. val AccountProBono )
        return $ acct^.AccountId
    return $ map (\(Value x) -> Probono x) xs

findAcademic :: MonadMerchant m => SqlPersistT m [Academic]
findAcademic = do
    xs <- select $ from $ \acct -> do
        where_ ( acct^.AccountType ==. val AccountAcademic )
        return $ acct^.AccountId
    return $ map (\(Value x) -> Academic x) xs

findTrial :: MonadMerchant m => SqlPersistT m [Trial]
findTrial = do
    xs <- select $ from $ \(acct, agr) -> do
        where_ ( agr^.AgreementItemType  ==. val TrialAgreement
             &&. agr^.AgreementItemState ==. val AgreementActive
             &&. agr^.AgreementAccount   ==. acct^.AccountId
               )
        return (acct^.AccountId, agr^.AgreementExpires)

    checkUniqueness "Trials" $ map (\(Value x, _) -> x) xs

    return $ map (\(Value x, Value e) ->
                   Trial x $ fromMaybe (error $ "x = " ++ ppShow x) e) xs

findPersonal :: MonadMerchant m => SqlPersistT m [Personal]
findPersonal = do
    xs <- select $ from $ \(acct, agr) -> do
        where_ ( acct^.AccountType       ==. val AccountPersonal
             &&. agr^.AgreementItemType  ==. val RegularAgreement
             &&. agr^.AgreementFrequency !=. val OneTimeOnly
             &&. agr^.AgreementAccount   ==. acct^.AccountId
               )
        return (acct^.AccountId, agr^.AgreementFrequency,
                agr^.AgreementNextBillDate)

    checkUniqueness "Personal" $ map (\(Value x, _, _) -> x) xs

    return $ map (\(Value x, Value f, Value n) ->
                   Personal x (case f of
                                    OneTimeOnly -> error "OneTimeOnly"
                                    DayOfMonth  -> Monthly
                                    DayOfYear   -> Annual) n) xs

findProfessional :: MonadMerchant m => SqlPersistT m [Professional]
findProfessional = do
    xs <- select $ from $ \(acct, agr) -> do
        where_ ( acct^.AccountType       ==. val AccountRegular
             &&. agr^.AgreementItemType  ==. val RegularAgreement
             &&. agr^.AgreementFrequency !=. val OneTimeOnly
             &&. agr^.AgreementAccount   ==. acct^.AccountId
               )
        return (acct^.AccountId, agr^.AgreementId, agr^.AgreementNextBillDate)

    checkUniqueness "Professional" $ map (\(Value x, _, _) -> x) xs

    for xs $ \(Value x, Value agrId, Value n) -> do
        ys <- select $ from $ \(acct, bundle, prod) -> do
            where_ ( acct^.AccountId ==. val x
                 &&. bundle^.LicenseBundleAgreement ==. val agrId
                 &&. prod^.ProductId ==. bundle^.LicenseBundleProduct
                   )
            return (prod^.ProductName, bundle^.LicenseBundleAssignee)

        let pn = case length $ nub $ map (\(Value p, _) -> p) ys of
                1 -> head $ map (\(Value p, _) -> p) ys
                _ -> error $ "Products: " ++ ppShow ys

        return $ Professional x pn n $ map (\(_, Value u) -> u) ys

getCurrentData :: MonadMerchant m
               => SqlPersistT m ([Probono], [Academic], [Trial], [Personal],
                                 [Professional])
getCurrentData = (,,,,) <$> findProbono
                        <*> findAcademic
                        <*> findTrial
                        <*> findPersonal
                        <*> findProfessional

main :: IO ()
main = runResourceT $ runNoLoggingT $ do
    merchant <- initializeMerchant defaultMerchantConfig
        { merchantProcessor    = ProcessorMockSource
        , merchantDatabaseType = ProductionDB
            (encodeUtf8 "dbname=merchant user=learning_site host=localhost") 16
        , merchantCurrentTime  = getCurrentTime
        , merchantSendMail     = error "Cannot send mail"
        }
    callMerchant merchant $ runMerchantDB $ do
        p <- findProbono
        liftIO $ putStrLn $ ppShow p
        a <- findAcademic
        liftIO $ putStrLn $ ppShow a
        t <- findTrial
        liftIO $ putStrLn $ ppShow t
        pers <- findPersonal
        liftIO $ putStrLn $ ppShow pers
        pro <- findProfessional
        liftIO $ putStrLn $ ppShow pro
