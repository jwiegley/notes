class (MonoFunctor c, MonoFunctor d) => MonoTransform c d where
    mtransform :: c -> d
instance (MonoFunctor c, MonoFoldable c,
          MonoFunctor d, FromList d,
          Convertible (Element c) (Element d))
         => MonoTransform c d where
    mtransform xs = fromList (foldr (\x -> (convert x :)) [] xs)
instance MonoTransform [Char] S.ByteString where
    mtransform = T.encodeUtf8 . T.pack
instance MonoTransform [Char] T.Text where
    mtransform = T.pack
instance MonoTransform [Char] L.ByteString where
    mtransform = TL.encodeUtf8 . TL.pack
instance MonoTransform [Char] TL.Text where
    mtransform = TL.pack
instance MonoTransform T.Text S.ByteString where
    mtransform = T.encodeUtf8
instance MonoTransform T.Text L.ByteString where
    mtransform = TL.encodeUtf8 . TL.fromStrict
instance MonoTransform TL.Text S.ByteString where
    mtransform = T.encodeUtf8 . TL.toStrict
instance MonoTransform TL.Text L.ByteString where
    mtransform = TL.encodeUtf8
instance MonoTransform S.ByteString [Char] where
    mtransform = T.unpack . T.decodeUtf8
instance MonoTransform T.Text [Char] where
    mtransform = T.unpack
instance MonoTransform L.ByteString [Char] where
    mtransform = TL.unpack . TL.decodeUtf8
instance MonoTransform TL.Text [Char] where
    mtransform = TL.unpack
instance MonoTransform S.ByteString T.Text where
    mtransform = T.decodeUtf8
instance MonoTransform L.ByteString T.Text where
    mtransform = TL.toStrict . TL.decodeUtf8
instance MonoTransform S.ByteString TL.Text where
    mtransform = TL.fromStrict . T.decodeUtf8
instance MonoTransform L.ByteString TL.Text where
    mtransform = TL.decodeUtf8
