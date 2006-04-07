-- File: Collect
-- Description: This module contains classes and implentations for
--              colllections and association lists.

module Collect((\\),
               Collection(..), single, isNotEmpty, notElemC,
               AssocList(..), foundI, setI, addListI,
               union, removeDoubles, 
               IL, indexedToListIL, listToIndexedIL, breakIL, filterIL, concIL,
               keysIL,
               Tree,
               TreeWithOrder, indexedToListTWO, breakTWO, takeTWO, keysTWO,
               ListsAndOTree, mkLAOT, unLAOT, makeLAOT, addLAOT, addMakeLAOT, 
               keysLAOT,
               ListsAndTree,
               findAL, foundAL, findAll, findAll3, partA) where

import HaTuple --(fst3,doSnd)
import General(pair,splitFilter)
import List((\\))

{-
       OVERVIEW
      
We define two important classes here,
  - Collection
  - AssocList
We use the class Collection for different representations of sets. There are
two implementations: by a list, and by a combination of lists and a tree.
The latter implementation allows for a much more efficient lookup.
We use class AssocList for representations of association lists.
These lists do have an order.
One important operation is the retrieval of the collection of keys occuring
in a 'AssocList'. This is illustrated in the following table:

   operation  | from (AssocList)  |  to (Collection)
  --------------------------------------------------
   keysIL     |      IL           |     []
   keysTWO    |   TreeWithOrder   |    Tree
   keysLAT    |   ListsAndOTree  |  ListsAndTree
-}

infixr 5 +++

-----------------
-- COLLECTIONS --
-----------------

-- Here, a collection is a set

-- We allow only collections of elements that have an order on them. This
-- allows for more efficient implementations.
-- (It would be more elegant to put this restriction in specific instances,
--  e.g. 
--       data Eq k => IL k v = IL [(k,v)]
--  but Gofer doesn't accept (the consequences of) this definition.)

class Collection c where
     -- basic operations
     empty :: Ord a => c a
     add :: Ord a => a -> c a -> c a
     isEmpty :: Ord a => c a -> Bool
     elemC :: Ord a => a -> c a -> Bool
     (+++) :: Ord a => [a] -> c a -> c a
     filterC :: Ord a => (a -> Bool) -> c a -> c a
     -- (||) and (&&) are associative, commutative and idempotent operations,
     -- so the result is independent of the representation of the collection.
     allC :: Ord a => (a -> Bool) -> c a -> Bool
     anyC :: Ord a => (a -> Bool) -> c a -> Bool
     toC :: Ord a => [a] -> c a
     removeC :: Ord a => c a -> a -> c a
     toList :: c a -> [a]

-- Definable functions on collections

single :: (Ord a, Collection c) => a -> c a
single a = add a empty

isNotEmpty :: (Ord a, Collection c) => c a -> Bool
isNotEmpty = not . isEmpty

notElemC :: (Ord a, Collection c) => a -> c a -> Bool
a `notElemC` as = not (a `elemC` as)
  
                                
-----------------------
-- ASSOCIATION LISTS --
-----------------------

class AssocList c where
     emptyI :: c k v
     -- Precondition for addIL (k,_) l:  k does not occur in l.
     addI :: Ord k => (k,v) -> c k v -> c k v
     findI :: Ord k => c k v -> k -> (Bool,v)
     -- findIIndex also returns an index in the list. It is not an
     -- absolute index, but can be used relative to another index to
     -- determine the freshest entry.
     findIIndex :: Ord k => c k v -> k -> (Bool,(v,Int))
     maxIndexI :: c k v -> Int
     isEmptyI :: c k v -> Bool
     -- updateI and removeI deliver as result a boolean that says whether
     -- the v was found, and the new AssocList
     updateI  :: Ord k => c k v -> k -> (v->v) -> (Bool,c k v)
     removeI :: Ord k => c k v -> k -> (Bool, c k v)
     mapI :: (v->w) -> c k v -> c k w
     headI :: Ord k => c k v -> (k,v)
     tailI :: Ord k => c k v -> c k v

-- foundI: deliver some default argument if not found
foundI :: (AssocList c,Ord k) => c k v -> v -> k -> (Bool,v)
foundI l def x = let (found,res) = findI l x in
                 (found,if found then res else def)

setI :: (AssocList c,Ord k) => c k v -> k -> v -> c k v
setI c k v = let (found,c') = updateI c k (const v) in
             if found then
                c'
             else
                addI (k,v) c

-- Precondition for addListI l1 l2:
--   No key of l1 occurs in l2
addListI :: (AssocList c,Ord k) => [(k,v)] -> c k v -> c k v  
addListI l il = foldr addI il l

-----------------------------------
-- I M P L E M E N T A T I O N S --
-----------------------------------
                         
-----------
-- LISTS --
-----------

-- We use lists as representations of sets, where elements may be
-- represented more than once.
        

instance Collection [] where
     empty = []
     add = (:)
     isEmpty = null
     elemC = elem
     (+++) = (++)
     filterC = filter
     allC = all
     anyC = any
     toC = id
     removeC as a = removeAll as a
     toList a = a

union :: [[a]] -> [a]
union [] = []
union (as:ass) = as ++ union ass
  
-- removeDoubles as  removes all double occurrences in as
removeDoubles :: Ord a => [a] -> [a]
removeDoubles [] = []
removeDoubles (a:as) = a: removeDoubles (removeAll as a)

-- removeAll as a  removes all occurrences of a from as
removeAll :: Ord a => [a] -> a -> [a]
removeAll as a = filter (/=a) as


----------------------------------------
-- ASSOCLIST :   IMPLEMENTED BY LISTS --
----------------------------------------
                                          
-- efficiency :
--   findI   : ord(n)
--   addI    : ord(1)
--   removeI : ord(n)
                                                    
data IL k v = IL [(k,v)]                            

updateList :: Ord k => [(k,v)] -> k -> (v->v) -> (Bool,[(k,v)])
updateList [] k f = (False,undefined)
updateList ((k',v):l) k f | k==k' = (True, (k',f v) : l)
updateList ((k',v):l) k f | otherwise = doSnd ((k',v):) (updateList l k f)               
instance AssocList IL where
     emptyI = IL []
     addI x (IL l) = IL (x:l)
     findI (IL l) x = let l' = map snd (filter ((x==).fst) l) in
                      (not (null l'), head l')
     findIIndex (IL l) x = let len =length l
                               l' = zip l [len,len-1..1] 
                               l'' = filter ((x==).fst.fst) l'
                               ((_,v),n) = head l'' in
                       (not (null l''),(v,n))
     maxIndexI (IL l) = length l
     isEmptyI (IL l) = null l
     updateI (IL l) k f = doSnd IL (updateList l k f)
     removeI (IL l) x = let (l',filtered) = splitFilter ((x/=).fst) l in
                        (not (null filtered), IL l')
     mapI f (IL l) = IL (map (doSnd f) l)
     headI (IL l) = head l
     tailI (IL l) = IL (tail l)


-- additional functions defined on ILs

indexedToListIL :: IL k v -> [(k,v)]
indexedToListIL (IL l) = l          

listToIndexedIL :: [(k,v)] -> IL k v
listToIndexedIL = IL


breakIL :: (k -> Bool) -> IL k v -> ([(k,v)],IL k v)
breakIL p (IL l) = doSnd IL (break (p.fst) l)

filterIL :: (v->Bool) -> IL k v -> IL k v
filterIL p (IL l) = IL (filter (p . snd) l)

concIL :: IL k v -> IL k v -> IL k v
concIL (IL l1) (IL l2) = IL (l1 ++ l2)
      
keysIL :: IL k v -> [k]
keysIL (IL l) = map fst l

------------------------------------------
-- COLLECTIONS :   IMPLEMENTED BY TREES --
------------------------------------------
                                          

data Tree a = Leaf | Node (Tree a) a (Tree a)
    
instance Functor Tree where
    fmap f Leaf = Leaf
    fmap f (Node t1 a t2) = Node (fmap f t1) (f a) (fmap f t2)

depth :: Tree a -> Int
depth Leaf = 0
depth (Node t1 a t2) = 1 + (depth t1 `max` depth t2)

tsize :: Tree a -> Int
tsize Leaf = 0
tsize (Node t1 a t2) = 1 + tsize t1 + tsize t2

emptyTree :: Tree r
emptyTree = Leaf
                   
isEmptyTree :: Tree r -> Bool
isEmptyTree Leaf = True
isEmptyTree _ = False
    
-- First, trees for collections
elemTree :: Ord k => k -> Tree k -> Bool
k `elemTree` Leaf = False
k `elemTree` (Node t1 k' t2) | k<k' = k `elemTree` t1
                             | k>k' = k `elemTree` t2
                             | otherwise = True



addCTree :: Ord k => k -> Tree k -> Tree k
addCTree k Leaf = Node Leaf k Leaf
addCTree k (Node t1 k' t2)
                     | k < k' = Node (addCTree k t1) k' t2
                     | k > k' = Node t1 k' (addCTree k t2)
                     | otherwise = Node t1 k t2

removeCTree :: Ord k => Tree k -> k -> Tree k
removeCTree Leaf k = Leaf
removeCTree (Node t1 k' t2) k | k < k' = Node (removeCTree t1 k) k t2
                              | k > k' = Node t1 k (removeCTree t2 k)
                              | k == k' = glueTrees t1 t2

  
filterTree :: Ord k => (k -> Bool) -> Tree k -> Tree k
filterTree p Leaf = Leaf
filterTree p (Node t1 k t2) = let t1' = filterTree p t1
                                  t2' = filterTree p t2 in
                              if p k then
                                 Node t1' k t2'
                              else
                                 glueTrees t1' t2'

-- glueTrees t1 t2 makes a new tree containing all elements of both t1 and t2.
-- Precondition: The biggest element of t1 is smaller than the smallest of t2
--               (biggest of Leaf = -inf, smallest of Leaf = +Inf)
glueTrees :: Tree k -> Tree k -> Tree k
glueTrees Leaf t2 = t2
glueTrees t1 t2 = let (k,t1') = removeBiggest t1 in
                Node t1' k t2

-- removeBiggest t  returns the biggest element of t and the rest of t
-- Precondition: not (isEmptyTree t)
removeBiggest :: Tree k -> (k, Tree k)
removeBiggest (Node t1 k Leaf) = (k,t1)
removeBiggest (Node t1 k t2) = let (k',t2') = removeBiggest t2 in
                                (k',Node t1 k t2')

allTree :: (k->Bool) -> Tree k -> Bool
allTree p Leaf = True
allTree p (Node t1 k t2) = p k && allTree p t1 && allTree p t2
                                  
anyTree :: (k->Bool) -> Tree k -> Bool
anyTree p Leaf = False
anyTree p (Node t1 k t2) = p k || anyTree p t1 || anyTree p t2
                          
addListToTree :: Ord k => [k] -> Tree k -> Tree k
addListToTree [] t = t
addListToTree (k:ks) t = addCTree k (addListToTree ks t)

instance Collection Tree where
     empty = emptyTree
     add = addCTree
     isEmpty = isEmptyTree
     elemC = elemTree
     (+++) = addListToTree
     filterC = filterTree
     allC = allTree
     anyC = anyTree
     removeC = removeCTree
  
treeToList :: Tree k -> [k]
treeToList Leaf = []
treeToList (Node t1 k t2) = k : (treeToList t1 ++ treeToList t2)


----------------------------------------
-- ASSOCLIST :   IMPLEMENTED BY TREES --
----------------------------------------
                                          



findTree :: Ord k => Tree (k,v) -> k -> (Bool,v)
findTree Leaf a = (False,undefined)
findTree (Node t1 (k',v) t2) k | k<k' = findTree t1 k
                               | k>k' = findTree t2 k
                               | otherwise = (True,v)
                           
addTree :: Ord k => (k,v) -> Tree (k,v) -> Tree (k,v)
addTree kv Leaf = Node Leaf kv Leaf
addTree kv@(k,v) (Node t1 kv'@(k',_) t2)
                     | k < k' = Node (addTree kv t1) kv' t2
                     | k > k' = Node t1 kv' (addTree kv t2)
                     | otherwise = Node t1 kv t2
              

updateTree :: Ord k => Tree (k,v) -> k -> (v->v) -> (Bool, Tree (k,v))
updateTree Leaf k f = (False,undefined)
updateTree (Node t1 kv'@(k',v') t2) k f
                     | k < k' = let (b,t1') = updateTree t1 k f in
                                (b, Node t1' kv' t2)
                     | k > k' = let (b,t2') = updateTree t2 k f in
                                (b, Node t1 kv' t2')
                     | otherwise = (True, Node t1 (k,f v') t2)

removeTree :: Ord k => Tree (k,v) -> k -> (Bool, Tree (k,v))
removeTree Leaf k = (False, Leaf)
removeTree (Node t1 kv@(k',v) t2) k 
                | k < k' = let (b,t1') = removeTree t1 k in
                           (b,Node t1' kv t2)
                | k > k' = let (b,t2') = removeTree t2 k in
                           (b,Node t1 kv t2')
                | k == k' = (True, glueTrees t1 t2)


-- We use this representation for the global context

data TreeWithOrder k v = TWO (Tree (k,(v,Int))) [k] Int
-- invariant for TWO t l:  the keys occuring in k and l are the same.
--                         The Int is bigger than all Ints in the tree.

-- efficiency :
--   findI   : ord(log(n))
--   addI    : ord(log(n))
--   removeI : ord(n)
instance AssocList TreeWithOrder where
     emptyI = TWO emptyTree [] 0
     addI (k,v) (TWO t l n) = TWO (addTree (k,(v,n)) t) (k:l) (n+1)
     findI (TWO t _ _) k = doSnd fst (findTree t k)
     findIIndex (TWO t _ _) k = findTree t k
     maxIndexI (TWO _ _ n) = n
     isEmptyI (TWO _ l _) = null l
     updateI (TWO t l n) k f = let (b,t') = updateTree t k (doFst f) in
                               (b,TWO t' l n)
     removeI (TWO t l n) k = let (b,t') = (removeTree t k) in
                             (b,TWO t' (l\\[k]) n)
                             -- Keep the same 'size'
     mapI f (TWO t l n) = TWO (fmap (doSnd (doFst f)) t) l n
     headI tl@(TWO t l _) = let h = head l in
                            (h, snd (findI tl h))
     tailI (TWO t l n) = let k = head l in 
                         TWO (snd (removeTree t k)) (tail l) (n-1)


-- additional functions defined on TreeWithOrders

indexedToListTWO :: Ord k => TreeWithOrder k v -> [(k,v)]
indexedToListTWO (TWO t l _) = map (\k -> (k,fst (snd (findTree t k)))) l

breakTWO :: Ord k => (k -> Bool) -> TreeWithOrder k v -> 
            ([(k,v)],TreeWithOrder k v)
breakTWO p (TWO t [] n) = ([],TWO t [] n)
breakTWO p tl@(TWO t (x:xs') n)
        | p x       = ([],tl)
        | otherwise = let (ys,zs) = breakTWO p (TWO (snd (removeTree t x)) xs' (n-1)) in
                      ((x,fst (snd (findTree t x))):ys,zs)

takeTWO :: Ord k => Int -> TreeWithOrder k v -> [(k,v)]
takeTWO n (TWO t l _) = map (\k -> (k,fst (snd (findTree t k)))) (take n l)
                

-- Corresponding collection of keys: ListAndTree                   
keysTWO :: TreeWithOrder k v -> Tree k  
keysTWO (TWO t _ _) = fmap fst t

------------------------------
-- ASSOCLIST: ListsAndOTree --
------------------------------

-- We use the following representation for the combination of a number of
-- local and one global context                      


data ListsAndOTree k v = LAOT [IL k v] (TreeWithOrder k v) 
                                                
mkLAOT (a,b) = LAOT a b      

unLAOT (LAOT as b) = (as,b)                                                

makeLAOT t = LAOT [] t

addLAOT l (LAOT ls t) = LAOT (l:ls) t

addMakeLAOT l t = LAOT [l] t

updateLAOT :: Ord k => ([IL k v], TreeWithOrder k v) -> k -> (v->v) -> 
             (Bool,([IL k v], TreeWithOrder k v))
updateLAOT ([], b) k f = doSnd (pair []) (updateI b k f)
updateLAOT (a:as, b) k f = let (found, a') = updateI a k f in
                           if found then
                              (True, (a':as, b))
                           else
                              doSnd (doFst (a:)) (updateLAOT (as,b) k f)

removeLAOT ([],b) k = doSnd (pair []) (removeI b k)
removeLAOT (a:as,b) k = let (found,a') = removeI a k in
                        if found then
                           (True, (a':as, b))
                        else
                           doSnd (doFst (a:)) (removeLAOT (as,b) k)

tailLAOT ([],b) = ([],tailI b)
tailLAOT (a:as,b) = if isEmptyI a then
                       doFst (emptyI:) (tailLAOT (as,b))
                    else
                       (tailI a : as,b)

-- all operations leave the structure (the number of lists) intact
instance AssocList ListsAndOTree where
    emptyI = LAOT [] emptyI
    addI kv (LAOT [] b) = LAOT [] (addI kv b)
    addI kv (LAOT (a:as) b) = LAOT (addI kv a : as) b
    findI (LAOT [] b) k = findI b k 
    findI (LAOT (a:as) b) k = let (found,v) = findI a k in
                              if found then
                                 (True,v)
                              else
                                 findI (LAOT as b) k 
    findIIndex (LAOT [] b) k = findIIndex b k
    findIIndex (LAOT (a:as) b) k = let (found,(v,n)) = findIIndex a k in
                                   if found then
                                      (found,(v,n+maxIndexI (LAOT as b)))
                                   else
                                      findIIndex (LAOT as b) k        
    maxIndexI (LAOT as b) = sum (map maxIndexI as) + maxIndexI b
    isEmptyI (LAOT as b) = all isEmptyI as && isEmptyI b
    updateI (LAOT as b) k f = doSnd mkLAOT (updateLAOT (as,b) k f)
    removeI (LAOT as b) k = doSnd mkLAOT (removeLAOT (as,b) k)
    mapI f (LAOT as b) = LAOT (map (mapI f) as) (mapI f b)
    headI (LAOT [] b) = headI b
    headI (LAOT (a:as) b) = if isEmptyI a then
                               headI (LAOT as b)
                            else
                               headI a
    tailI (LAOT as b) = mkLAOT (tailLAOT (as,b))

-- additional function on ListsAndOTree's
keysLAOT :: Ord k => ListsAndOTree k v -> ListsAndTree k
keysLAOT (LAOT as t) = LAT (map keysIL as) (keysTWO t)

  
------------------------------
-- COLLECTION: ListAndTree  --
------------------------------
                            

data ListsAndTree k = LAT [[k]] (Tree k)

-- all operations leave the structure (the number of lists) intact
instance Collection ListsAndTree where
     empty = LAT [] empty
     add a (LAT [] t) = LAT [] (add a t)
     add x (LAT (a:as) t) = LAT (add x a : as) t
     isEmpty (LAT as t) = all isEmpty as && isEmpty t
     a `elemC` (LAT as t) = any (a `elemC`) as || a `elemC` t
     l +++ (LAT [] t) = LAT [] (l+++t)
     l +++ (LAT (a:as) t) = LAT ((l+++a) : as) t
     filterC p (LAT as t) = LAT (map (filterC p) as) (filterC p t)
     allC p (LAT as t) = all (allC p) as && allC p t
     anyC p (LAT as t) = any (anyC p) as || anyC p t
     toC a = LAT [toC a] empty
     removeC (LAT as t) k = LAT (map (flip removeC k) as) (removeC t k)
     toList (LAT as t) = concat (map toList as) ++ toList t
             



---------------------------------------
-- ASSOCIATION LIST AS LIST OF PAIRS --
---------------------------------------

 
findAL :: Ord a => [(a,b)] -> a -> (Bool,b)
findAL l x = let l' = map snd (filter ((x==).fst) l)
                 empty = null l' in
             (not empty, head l')

foundAL :: Ord a => [(a,b)] -> b -> a -> (Bool,b)
foundAL l def x = let (found,res) = findAL l x in
                (found, if found then res else def)
 


findAll :: Ord k => [(k,v)] -> k -> [v]
findAll l x = map snd (filter ((x==).fst) l)

findAll3 :: Ord k => [(k,v,w)] -> k -> [(v,w)]
findAll3 l x = map (\(_,b,c) -> (b,c)) (filter ((x==).fst3) l)             
  

-- partA l p  returns all elements of l for which key is in p
partA :: Ord k => [(k,v)] -> [k] -> [(k,v)]
partA l p = filter (\(k,_) -> k `elem` p) l

