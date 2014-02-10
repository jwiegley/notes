newtype ByteString64 = ByteString64 { unByteString64 :: ByteString }
    deriving (Eq, Read, Show, Data, Typeable,
#ifndef FAY
              Ord, Serialize, Generic, Hashable
#endif
             )
