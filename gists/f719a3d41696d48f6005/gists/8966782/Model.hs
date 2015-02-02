class FromModelId a b | a -> b where
    fromModelId :: DB.Key a -> b

class ToModelId a b | a -> b where
    toModelId :: b -> DB.Key a

instance FromModelId Project API.ProjectId where
    fromModelId (DB.Key (DB.PersistInt64 pid)) = API.ProjectId pid
    fromModelId _ = error "fromModelId for ProjectId failed"

instance ToModelId Project API.ProjectId where
    toModelId (API.ProjectId pid) = DB.Key $ DB.PersistInt64 pid

instance FromModelId RunConfig API.RunConfigId where
    fromModelId (DB.Key (DB.PersistInt64 pid)) = API.RunConfigId pid
    fromModelId _ = error "fromModelId for RunConfigId failed"

instance ToModelId RunConfig API.RunConfigId where
    toModelId (API.RunConfigId pid) = DB.Key $ DB.PersistInt64 pid
