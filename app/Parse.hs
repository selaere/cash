module Parse where
  
import Data.Void (Void)
import Text.Megaparsec
import Data.Text (Text)
import qualified Data.Char as Char
import Text.Megaparsec.Char (space1)
import Text.Megaparsec.Char.Lexer (decimal)
import qualified Data.Text as T
import Control.Monad (void, guard)
import Control.Applicative ((<**>))
import Data.Functor ((<&>))
import Text.Megaparsec.State (initialPosState)

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
sc = skipMany (hidden space1)

type Ident = Text


data Obj = Numlit Integer
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
  a <- takeWhileP (Just "continuation character") isContinuation
  b <- choice
    ([ guard (not (T.null a))
      *> (Cmd <$ lookAhead
        (void (single '(') <|> void (single ')') <|> space1 <|> void eof))
    , flip Literal <$> parseLit
    , \case
        '{' -> OPush
        '|' -> OPeek
        '}' -> OPop
        x   -> Cmd . flip T.snoc x
      <$> ending ] :: [Parser (Ident -> Obj)])
  pure (b a)
  where
    ending = label "ending character" (satisfy \x ->
      not (Char.isSpace x || Char.isControl x || x == ']' || x == ')'))

getPosition :: Parser Position
getPosition = getParserState <&> \x -> 
  Position ((sourceName.pstateSourcePos.statePosState) x) (stateOffset x)

parseTok :: Parser Tok
parseTok = Tok <$> getPosition <*> choice
  ([ Numlit <$> decimal
  , (single '$' *> parseIdent) >>= \case
      Cmd name -> return (LitLabel name)
      _        -> fail "?xyz[] is invalid"
  , single '(' *> sc *> many parseTok
    <**> (QuotF <$ single ')' <|> QuotUnf <$ eof)
  , parseIdent
  ] :: [Parser Obj]) <* sc

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