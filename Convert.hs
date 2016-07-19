{-# LANGUAGE OverloadedStrings #-}

import Control.Lens
import Text.XML
import Text.XML.Lens

main = do
    doc <- Text.XML.readFile
               (def { psDecodeEntities = decodeHtmlEntities })
               "whatthoughtsmaycome.wordpress.2016-07-19.xml"
    print $ doc ^.. root . el "rss"
        ./ el "channel"
        ./ el "item"
        ./ el "title" . text
