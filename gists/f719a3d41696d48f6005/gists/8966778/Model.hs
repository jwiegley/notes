class MonoPointed mono where
    opoint :: Element mono -> mono

toModelId :: (MonoFoldable a, Element a ~ Int64) => a -> DB.Key b
toModelId k = DB.Key $ PersistInt64 $ headEx $ otoList k

fromModelId :: (MonoPointed b, Element b ~ Int64) => DB.Key a -> b
fromModelId (DB.Key (DB.PersistInt64 pid)) = opoint pid
fromModelId _ = error "fromModelId failed"

type instance Element API.ProjectId = Int64
instance MonoPointed API.ProjectId where
    opoint = API.ProjectId

type instance Element API.RunConfigId = Int64
instance MonoPointed API.RunConfigId where
    opoint = API.RunConfigId
