module Parse where
  
import Data.Void (Void)
import Text.Megaparsec
import Data.Text (Text)
import qualified Data.Char as Char
import Text.Megaparsec.Char (space1)
import Text.Megaparsec.Char.Lexer (decimal)
import qualified Data.Text as Text
import Control.Monad (void, guard)
import Control.Applicative ((<**>))

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
         | QuotF [Obj]
         | QuotUnf [Obj]
         | OPush Ident
         | OPeek Ident
         | OPop  Ident
         | Literal Ident Text
  deriving Show



parseLit :: Parser Text
parseLit = single '[' *> (Text.concat <$> many things) <* (void (single ']') <|> eof)
  where
    things = (takeWhile1P Nothing \x-> x /= ']' && x /= '[')
      <|> (Text.cons '[' . flip Text.snoc ']' <$> parseLit)

parseIdent :: Parser Obj
parseIdent = do
  a <- takeWhileP (Just "continuation character") isContinuation
  b <- choice
    [ guard (not (Text.null a))
      *> (Cmd <$ lookAhead
        (void (single '(') <|> void (single ')') <|> space1 <|> void eof))
    , flip Literal <$> parseLit
    , \case
        '{' -> OPush
        '\\'-> OPeek
        '}' -> OPop
        x   -> Cmd . flip Text.snoc x
      <$> ending ]
  pure (b a)
  where
    ending = label "ending character" (satisfy \x ->
      not (Char.isSpace x || Char.isControl x || x == ']' || x == ')'))


parseObj :: Parser Obj
parseObj = choice
  [ Numlit <$> decimal
  -- , (single '?' *> parseIdent) >>= \case
  --     Cmd name -> return (LitLabel name)
  --     _         -> fail "?xyz[] is invalid"
  , single '(' *> sc *> many parseObj
    <**> (QuotF <$ single ')' <|> QuotUnf <$ eof)
  , parseIdent
  ] <* sc

parseFile :: Parser [Obj]
parseFile = sc *> many parseObj <* eof

parse :: Text -> IO [Obj]
parse input = case runParser parseFile "[bees]" input of
  Left errorbundle -> putStrLn (errorBundlePretty errorbundle) >> fail "owie"
  Right val -> pure val