
module Meriv.Types.Dynamic where

import GHC.TypeLits
import Data.Typeable
import Data.Void
import GHC.Generics
import Prelude (String, Maybe(..), Either(..), pure, ($))
import qualified BasePrelude as BP

-- Given a list of types and a list of entities, attempt to parse
-- them into a complete MerivSchema.
parseMerivSchema :: [String] -> [(String, String)] -> Maybe SomeMerivSchema
parseMerivSchema ts es =
  case parseSchema ts of
    SomeSchema sP typeParser ->
      case (parseEntities sP typeParser es) of
        Just (SomeEntityParser eP entityParser) ->
          pure $ SomeMerivSchema sP eP typeParser entityParser

data SomeMerivSchema = forall s e. SomeMerivSchema (Proxy s) (Proxy e) (TypeParser s) (EntityParser s e)

data EntityDecl s (x :: Symbol) (t :: s) (a :: s) where
  EntityDecl :: EntityDecl s x t t

data SchemaEntry (x :: Symbol)
  = SchemaEntry

type TypeParser s = String -> Maybe (SomeType s)

data SomeSchema = forall s. SomeSchema (Proxy s) (TypeParser s)

data SomeType s = forall (t :: s). SomeType (Proxy t) s

data SomeType1 s = forall (e :: s -> *). SomeType1 (Proxy e)

-- Helper function to obtain a proxy for the SchemaEntry type.
getTypeProxy :: forall (x :: Symbol). Proxy x -> Proxy (SchemaEntry x)
getTypeProxy _ = Proxy

-- Helper function to obtain a proxy for the value-level SchemaEntry.
getValueProxy :: forall (x :: Symbol). Proxy x -> Proxy ('SchemaEntry :: SchemaEntry x)
getValueProxy _ = Proxy

-- Helper function to obtain a value-level SchemaEntry from a proxy for
-- the appropriate symbol.
getSchemaEntry :: forall (x :: Symbol). Proxy x -> SchemaEntry x
getSchemaEntry _ = SchemaEntry

-- | Generate a simple schema type from a string.
getType :: String -> SomeSchema
getType x = asType $ someSymbolVal x

-- | Generate a simple schema type from a symbol.
asType :: SomeSymbol -> SomeSchema
asType (SomeSymbol s) = SomeSchema (getTypeProxy s)
  (\x -> if x BP.== symbolVal s
    then pure $ SomeType (getValueProxy s) (getSchemaEntry s)
    else Nothing)

-- Helper function to combine two schemas by taking their union.
eitherS :: SomeSchema -> SomeSchema -> SomeSchema
eitherS (SomeSchema xP x) (SomeSchema yP y) = SomeSchema (eitherP xP yP) (eitherD x y)

-- Helper function to apply `Either` at the proxy level.
eitherP :: forall (x :: *) (y :: *). Proxy x -> Proxy y -> Proxy (Either x y)
eitherP _ _ = Proxy

-- Helper function to apply `Left` at the proxy level.
leftP :: Proxy x -> Proxy ('Left x)
leftP _ = Proxy

-- Helper function to apply `Right` at the proxy level.
rightP :: Proxy x -> Proxy ('Right x)
rightP _ = Proxy

-- Helper function to lift two type parsers into a sum.
eitherD :: TypeParser x -> TypeParser y -> TypeParser (Either x y)
eitherD f g = \x ->
  case (f x) of
    Just (SomeType resP res) -> pure $ SomeType (leftP resP) (Left res)
    Nothing ->
      case (g x) of
        Just (SomeType resP res) -> pure $ SomeType (rightP resP) (Right res)
        Nothing -> Nothing

-- Here's an example of how to parse a raw schema into a
-- type (wrapped in an existential) that only exists in runtime.
parseSchema :: [String] -> SomeSchema
parseSchema [] = SomeSchema (Proxy @Void) (\_ -> Nothing)
parseSchema (x:xs) = eitherS (getType x) (parseSchema xs)

-- Note: Here I'll need access to a parser for types as well.
parseEntities :: forall s. Proxy s -> TypeParser s -> [(String, String)] -> Maybe (SomeEntityParser s)
parseEntities _ typeParser ((x,y):[]) = do
  t <- typeParser y
  case t of
    (SomeType tP tV) -> 
      pure $ getEntityType tP tV x
parseEntities sP typeParser ((x,y):xs) = do
  -- Try to parse the type annotation.
  t <- typeParser y
  -- If it succeeds, continue to obtain the entity parser.
  case t of
    (SomeType tP tV) -> do
      ep1 <- parseEntities sP typeParser xs
      let ep2 = getEntityType tP tV x
      pure (ep1 `combineEntities` ep2)

getEntityType :: forall (s :: *) (t :: s). Proxy t -> s -> String -> SomeEntityParser s
getEntityType _ typ name = SomeEntityParser
    (Proxy @(EntityDecl s "" t))
    (EntityParser $ \x ->
       if x BP.== name
       then pure $ SomeEntity EntityDecl
       else Nothing)

combineEntities :: SomeEntityParser s -> SomeEntityParser s -> SomeEntityParser s
combineEntities (SomeEntityParser _ p1) (SomeEntityParser _ p2)
  = (SomeEntityParser Proxy (joinParsers p1 p2))

joinParsers :: EntityParser s e1 -> EntityParser s e2 -> EntityParser s (e1 :+: e2)
joinParsers (EntityParser p1) (EntityParser p2) = EntityParser $ \x ->
  case p1 x of
    Just (SomeEntity res) -> pure $ SomeEntity $ L1 res
    Nothing -> case p2 x of
      Just (SomeEntity res) -> pure $ SomeEntity $ R1 res
      Nothing -> Nothing

data SomeEntity s e = forall (t :: s). SomeEntity (e t)

data EntityParser s e = EntityParser (String -> Maybe (SomeEntity s e))

data SomeEntityParser s = forall e. SomeEntityParser (Proxy e) (EntityParser s e)

