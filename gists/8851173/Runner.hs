instance Typeable a => Typeable (Last a) where
    typeOf (Last x) = typeOf x
instance (Data a, Typeable a) => Data (Last a) where
    gunfold f g x       = undefined     -- jww (2014-02-06): :Migrate: NYI
    toConstr (Last x)   = toConstr x
    dataTypeOf (Last x) = dataTypeOf x
