-- {-# LANGUAGE OverloadedStrings #-}

module TryNet where

import Text.HTML.Scalpel
import Text.Read (Lexeme(String))

-- >>> getHeadText
-- Just "Example Domain"
getHeadText :: IO (Maybe String)
getHeadText = scrapeURL "http://example.com" getHead
  where
    getHead = chroot (tagSelector "div") $
      text $ tagSelector "h1"

-- >>> getPTexts
-- Just ["This domain is for use in illustrative examples in documents. You may use this\n    domain in literature without prior coordination or asking for permission.","More information..."]
getPTexts :: IO (Maybe [String])
getPTexts = scrapeURL "http://example.com" {- Put the DOM tree into the next function -} $
  fmap concat $ chroots (tagSelector "div") $ 
  -- Put all the selected parts into the next element 
  -- if use chroot, put only the first match into the next monadic part
  -- the monadic element is exactly the running context of the next value
  fmap concat $ chroots (tagSelector "p") $ 
  -- with "s" at the end of the name of the functions means to match ALL elements
  -- without "s" means to match just the FIRST element
  texts textSelector
    



-- play with BitTorrent Web

bitTorrentWeb :: IO (Maybe [String])
bitTorrentWeb = scrapeURL "http://127.0.0.1:38565/gui/index.html?v=1.2.9.4937&localauth=localapiddf584f1df8d8b92:#/library" toCap
  where
    toCap :: Scraper String [String]
    toCap = texts (tagSelector "script")
      -- fmap concat $ chroots (tagSelector "div") $ texts textSelector
