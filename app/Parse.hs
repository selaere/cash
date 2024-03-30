module Parse where

import Data.Void (Void)
import Text.Megaparsec
import Data.Text (Text)
import qualified Data.Char as Char
import Text.Megaparsec.Char (space1)
import Text.Megaparsec.Char.Lexer (decimal, skipLineComment)
import qualified Data.Text as T
import Control.Monad (void, guard)
import Control.Applicative ((<**>))
import Data.Functor ((<&>), ($>))
import Text.Megaparsec.State (initialPosState)
import Data.Char (isDigit, digitToInt)

type Parser = Parsec Void Text

infixr 8 .:
(.:) :: (c->d) -> (a->b->c) -> a->b->d
(f .: g) x y = f (g x y)

isContinuation :: Char -> Bool
isContinuation c = c == '_' || case Char.generalCategory c of
  Char.LowercaseLetter -> True
  Char.ModifierLetter  -> True
  Char.OtherLetter     -> True
  Char.DecimalNumber   -> True
  _ -> False

sc :: Parser ()
sc = skipMany (hidden (space1 <|> skipLineComment "_ "))

text3 :: Char -> Char -> Char -> T.Text
text3 x y z = T.pack [x,y,z]

type Ident = Text


data Obj = Numlit Rational
         | Numlits [Rational]
         | Cmd Ident
         | LitLabel Ident
         | QuotF [Tok]
         | QuotUnf [Tok]
         | OPush Ident
         | OPeek Ident
         | OPop  Ident
         | Literal Ident Text
  deriving Show

data Position = Position !FilePath !Int
  deriving (Eq, Show)

data Tok = Tok !Position Obj
  deriving Show


parseLit :: Parser Text
parseLit = single '[' *> (T.concat <$> many things) <* (void (single ']') <|> eof)
  where
    things = (takeWhile1P Nothing \x-> x /= ']' && x /= '[')
      <|> (T.cons '[' . flip T.snoc ']' <$> parseLit)

parseIdent :: Parser Obj
parseIdent = do
  head <- label "identifier head" heading
  choice
    [ guard (not (T.null head))
      *> lookAhead (void (single '(') <|> void (single ')') <|> space1 <|> void eof)
      $> Cmd head
    , Literal head <$> parseLit
    , \case
        '{' -> OPush head
        '|' -> OPeek head
        '}' -> OPop  head
        x   -> Cmd (T.snoc head x)
      <$> label "identifier ending" (satisfy ending) ]
  where
    heading = T.concat <$> many (
          takeWhile1P Nothing isContinuation
      <|> try (text3 <$> satisfy ending
                     <*> single '_'
                     <*> satisfy \x -> (ending x || isContinuation x) && not (isDigit x)) )
    ending x = not (Char.isSpace x || Char.isControl x || x == ']' || x == ')')

getPosition :: Parser Position
getPosition = getParserState <&> \x ->
  Position ((sourceName.pstateSourcePos.statePosState) x) (stateOffset x)

parseNum :: Parser Obj
parseNum = label "number literal" (strand <$> signed `sepBy1` single '_')
  where
    strand :: [Rational] -> Obj
    strand [x] = Numlit x
    strand xs  = Numlits xs
    
    signed :: Parser Rational
    signed =
      option id (single '_' $> negate)                                          -- sign
      <*> ( (+)
            <$> decimal                                                             -- integer part
            <*> option 0 (try $ single '.' *> (makeFrac <$> some (satisfy isDigit)))-- rational part
          )
      where makeFrac = foldr (\x y->((toRational.digitToInt) x + y) / 10) 0

parseTok :: Parser Tok
parseTok = Tok <$> getPosition <*> tok <* sc
  where tok = choice
          [ parseNum
          , (single '$' *> parseIdent) >>= \case
              Cmd name -> return (LitLabel name)
              _        -> fail "$xyz[] is invalid"
          , single '(' *> sc *> many parseTok
            <**> (QuotF <$ single ')' <|> QuotUnf <$ eof)
          , parseIdent
          ]

parseFile :: Parser [Tok]
parseFile = sc *> many parseTok <* eof

parse :: String -> Text -> IO [Tok]
parse filename input = case runParser parseFile filename input of
  Left errorbundle -> putStrLn (errorBundlePretty errorbundle) >> fail "owie"
  Right val -> pure val

formatLine :: Text -> FilePath -> Int -> Text
formatLine src name n =
  let (line, pos) = reachOffset n (initialPosState name src)
  in "at "<>T.pack (sourcePosPretty (pstateSourcePos pos))<>"\n  |"<>T.pack (concat line)<>"\n"
