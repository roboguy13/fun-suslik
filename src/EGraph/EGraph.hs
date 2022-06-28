-- Inspired by 'egg: Fast and Extensible Equality Saturation' by Willsey et al.

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module EGraph.EGraph
  where

import           Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NonEmpty

import           Control.Monad

import           Data.Semigroup
import           Data.Data

-- import           Data.STRef
import           Control.Monad.ST.Trans
import           Control.Monad.Trans
import           Control.Monad.State

import           Data.Equivalence.STT (Class, Equiv)
import           Data.Equivalence.Monad

import           Data.Set (Set)
import qualified Data.Set as Set

import           Data.Map (Map)
import qualified Data.Map as Map

import           EGraph.Rewrite
import           Representation.Parts

newtype EClassId = EClassId { getEClassId :: Int }
  deriving (Eq, Ord, Show)

data EClass a =
  EClass
  { eclassId :: EClassId
  , eclassNodes :: Set (ENode a)
  , eclassParents :: Set (ENode a, EClassId)
  }
  deriving (Show)

instance Ord (EClass a) where
  compare x y = compare (eclassId x) (eclassId y)

instance Eq (EClass a) where
  x == y = eclassId x == eclassId y

data ENode a =
  ENode
  { enodeFun :: a
  , enodeChildren :: [EClassId]
  }
  deriving (Eq, Ord, Show)

type EClassEquiv s = Equiv s (Set EClassId) EClassId

type EHashcons n = Map (ENode n) EClassId -- Should this be multiple EClassId's?
type EClassMap n = Map EClassId (EClass n)

data EGraphState n =
  EGraphState
  { hashcons :: EHashcons n
  , eclasses :: EClassMap n
  , nextClassId :: EClassId
  , workList :: [EClassId]
  }
  deriving Show

emptyEGraphState :: Ord n => EGraphState n
emptyEGraphState =
  EGraphState mempty mempty (EClassId 0) mempty

newtype EGraphM s n a =
  EGraphM
    { getEGraphM :: EquivT s (Set EClassId) EClassId (State (EGraphState n)) a }
  deriving (Functor, Applicative, Monad, MonadState (EGraphState n))

type EGraph s = Set (EClass s)

class (ToParts n, Ord n) => GraphNode n where
  nodeCost :: n -> Int

-- | Used internally to construct the initial e-graph
constructENode :: (GraphNode n) => n -> EGraphM s n EClassId
constructENode n = do
  childClassIds <- mapM constructENode (nodeChildren n)

  snd <$> addENode (ENode n childClassIds)

runEGraphM :: (GraphNode n) => n -> (forall s. EGraphM s n a) -> (a, EGraphState n)
runEGraphM node act =
  flip runState emptyEGraphState $
    runEquivT Set.singleton mempty $
      getEGraphM $ do
        constructENode node 
        x <- act
        classMap <- eclasses <$> get
        rebuildEGraph
        pure x

workListPop :: EGraphM s n (Maybe EClassId)
workListPop = 
  fmap workList get >>= \case
    [] -> pure Nothing
    (x:xs) -> do
      modify (\z -> z { workList = xs })
      pure (Just x)

workListPush :: EClassId -> EGraphM s n ()
workListPush ident = modify (\x -> x { workList = ident : workList x })

-- | Fully pop worklist
workListTake :: EGraphM s n [EClassId]
workListTake = go
  where
    go =
      workListPop >>= \case
        Nothing -> pure []
        Just x -> do
          (x:) <$> go

whileHasWorkList :: EGraphM s n () -> EGraphM s n ()
whileHasWorkList m = go
  where
    go = do
      b <- not . null . workList <$> get
      if b
      then m *> go
      else pure ()

getHashcons :: EGraphM s n (EHashcons n)
getHashcons = hashcons <$> get

modifyHashcons :: (EHashcons n -> EHashcons n) -> EGraphM s n ()
modifyHashcons f = modify (\x -> x { hashcons = f (hashcons x) })

hashconsLookup :: Ord n => ENode n -> EGraphM s n (Maybe EClassId)
hashconsLookup enode = Map.lookup enode <$> getHashcons

hashconsInsert :: Ord n => ENode n -> EClassId -> EGraphM s n ()
hashconsInsert enode classId = modifyHashcons (Map.insert enode classId)

hashconsRemove :: Ord n => ENode n -> EGraphM s n ()
hashconsRemove enode = modifyHashcons (Map.delete enode)

updateEClasses :: Ord n => (EClassMap n -> EClassMap n) -> EGraphM s n ()
updateEClasses f = modify (\x -> x { eclasses = f (eclasses x) })

lookupEClass :: Ord n => EClassId -> EGraphM s n (EClass n)
lookupEClass ident =
  fmap (Map.lookup ident . eclasses) get >>= \case
    Nothing -> error $ "lookupEClass: Cannot find " ++ show ident
    Just eclass -> pure eclass

setEClass :: Ord n => EClassId -> EClass n -> EGraphM s n ()
setEClass classId eclass = updateEClasses (Map.insert classId eclass)

modifyEClass :: Ord n => EClassId -> (EClass n -> EClass n) -> EGraphM s n ()
modifyEClass classId f = updateEClasses (Map.adjust f classId)

eclassPushParent :: Ord n => EClass n -> (ENode n, EClassId) -> EClass n
eclassPushParent eclass newParent = eclass { eclassParents = Set.insert newParent (eclassParents eclass) }

freshEClassId :: EGraphM s n EClassId
freshEClassId = do
  classId@(EClassId n) <- nextClassId <$> get
  modify (\x -> x { nextClassId = EClassId (succ n) })
  pure classId

newSingletonEClass :: Ord n => ENode n -> EGraphM s n (EClass n)
newSingletonEClass enode = do
  classId <- freshEClassId
  let eclass =
        EClass
          { eclassId = classId
          , eclassNodes = Set.singleton enode
          , eclassParents = mempty
          }
  setEClass classId eclass
  pure eclass

-- findEClass :: EClassId -> EGraphM s n (EClass n)
-- findEClass ident = undefined

-- addParent :: ENode n -> ENode n -> ENode n
-- addParent enode newParent = enode { parents


mergeIds :: EClassId -> EClassId -> EGraphM s n EClassId
mergeIds ident1 ident2 = do
  EGraphM $ equate ident1 ident2
  efind ident1 -- TODO: Is this efficient enough?


efind :: EClassId -> EGraphM s n EClassId
efind ident = do
  x <- EGraphM (desc =<< getClass ident)
  pure (Set.findMin x)

-- efindClass :: EClass n -> EGraphM s n (EClass n)
-- efindClass = undefined

canonicalize :: ENode n -> EGraphM s n (ENode n)
canonicalize (ENode fun args) =
  ENode fun <$> mapM efind args

addENode :: Ord n => ENode n -> EGraphM s n (ENode n, EClassId)
addENode enode0 = do
  enode <- canonicalize enode0

  hashconsLookup enode >>= \case
    Just c0 -> do
      c <- efind c0
      pure (enode, c)
    Nothing -> do
      eclass <- newSingletonEClass enode
      let ident = eclassId eclass

      forM_ (enodeChildren enode) $ \child ->
        modifyEClass child (`eclassPushParent` (enode, ident))

      hashconsInsert enode ident
      pure (enode, ident)

merge :: Ord n => EClassId -> EClassId -> EGraphM s n EClassId
merge ident1 ident2 = do
  foundIdent1 <- efind ident1
  foundIdent2 <- efind ident2

  if foundIdent1 == foundIdent2
  then pure foundIdent1
  else do
    newIdent <- mergeIds ident1 ident2

    workListPush newIdent
    pure newIdent

rebuildEGraph :: Ord n => EGraphM s n ()
rebuildEGraph =
  whileHasWorkList $ do
    todo <- mapM (lookupEClass <=< efind) =<< workListTake

    forM_ todo $ \eclass ->
      repair eclass

repair :: forall n s. Ord n => EClass n -> EGraphM s n ()
repair eclass = do
  forM_ (eclassParents eclass) $ \(p_node0, p_eclass) -> do
    hashconsRemove p_node0
    p_node <- canonicalize p_node0
    hashconsInsert p_node =<< efind p_eclass

  newParents <- go mempty (Set.toList (eclassParents eclass))
  modifyEClass (eclassId eclass) $
    \x -> x { eclassParents = Set.fromList (Map.toList newParents) }
  where
    go :: Map (ENode n) EClassId -> [(ENode n, EClassId)] -> EGraphM s n (Map (ENode n) EClassId)
    go newParents [] = pure newParents
    go newParents ((p_node, p_eclass):rest) = do
      case Map.lookup p_node newParents of
        Just foundEClass -> void $ mergeIds p_eclass foundEClass
        Nothing -> pure ()

      canonEClass <- efind p_eclass
      go (Map.insert p_node canonEClass newParents) rest

type Subst n = [(String, n)]

ematch :: n -> EGraphM s n (Subst n, EClass n)
ematch = undefined

-- type NodeRef s a = STRef s (Node s a)
--
-- type EClass s a = NonEmpty (NodeRef s a)
--
-- type EClassRef s a = STRef s (EClass s a)
--
-- data Node s a
--   = Node
--     { nodeLabel :: a
--     , nodeArgs :: [EClassRef s a]
--     }
--
-- type EGraph s a = [EClass s a]
--
-- data Rewrite s a = Rewrite { getRewrite :: EGraph s a -> EGraph s a }
--
