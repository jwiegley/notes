instance ToJSON UpdateActions where
    toJSON (UpdateActions upds newt) =
        object [ "_uaUpdates"   .= toJSON (toList upds)
               , "_uaNewTarget" .= toJSON newt
               ]
instance FromJSON UpdateActions where
    parseJSON (Object v) = UpdateActions
        <$> (fromList <$> v .: "_uaUpdates")
        <*> v .: "_uaNewTarget"
