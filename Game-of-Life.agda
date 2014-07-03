open import Data.Bool
  hiding (_≟_)
open import Data.Nat
open import Data.Fin
  using (Fin ; zero ; suc)
open import Data.Vec
open import Data.Product
  hiding (map)

open import Function

open import Relation.Nullary.Decidable
  hiding (map)

module Game-of-Life where

data Cell : Set where
  alive : Cell
  dead  : Cell

-- conversion for counting neighbors
cellToNat : Cell → ℕ
cellToNat alive = 1
cellToNat dead  = 0

-- directions
data Dir : Set where
  Same  : Dir
  Left  : Dir
  Right : Dir

finToDir : Fin 3 → Dir
finToDir zero             = Same
finToDir (suc zero)       = Left
finToDir (suc (suc zero)) = Right
finToDir (suc (suc (suc ())))

-- world and location in it
Grid : ℕ → ℕ → Set
Grid m n = Vec (Vec Cell n) m

SqGrid : ℕ → Set
SqGrid n = Grid n n

CellLoc : ℕ → ℕ → Set
CellLoc m n = (Fin m × Fin n) 

lookup-grid : ∀ {m n} → CellLoc m n → Grid m n → Cell
lookup-grid (x , y) g = lookup y (lookup x g)

-- shifting the grid
shift₁ : ∀ {A : Set} {n} → Dir → A → Vec A n → Vec A n
shift₁ _ _ [] = []
shift₁ Same     _ v     = v
shift₁ Left  a (x ∷ xs) = xs ∷ʳ a
shift₁ Right a (x ∷ xs) = a ∷ init (x ∷ xs)

hshift : ∀ {m n} → Grid m n → Dir → Grid m n
hshift g d = map (shift₁ d dead) g

vshift : ∀ {m n} → Grid m n → Dir → Grid m n
vshift g d = shift₁ d (replicate dead) g

-- shift the entire grid
shiftGrid : ∀ {m n} → Grid m n → (Dir × Dir) → Grid m n
shiftGrid g (x , y) = vshift (hshift g x) y

forloop = tabulate
syntax forloop (λ x → y) = for x yield y

-- all possible shifts, represented as a Vec of Grids
all-shifts : ∀ {m n} → Grid m n → Vec (Grid m n) 9
all-shifts g = concat 
  (for i yield
   for j yield
     let i' = finToDir i
         j' = finToDir j
     in shiftGrid g (i' , j'))

neighbor-shifts : ∀ {m n} → Grid m n → Vec (Grid m n) 8
neighbor-shifts g = tail (all-shifts g)

neighbor-count : ∀ {m n} → CellLoc m n → Grid m n → ℕ
neighbor-count {zero} {_} (() ,  y) g
neighbor-count {_} {zero} (x  , ()) g
neighbor-count {suc m} {suc n} l g = 
  foldr₁ _+_ $ map (λ g' → cellToNat $ lookup-grid l g')
                   (neighbor-shifts g)

-- rules of the game
update' : Cell → ℕ → Cell
update' alive ns = if ({!ns ≥ 2!}) ∧ ({!ns ≤ 3!}) then alive else dead
update' dead  ns = if ⌊ ns ≟ 3 ⌋  then alive else dead

-- update the whole grid once
update-grid : ∀ {m n} → Grid m n → Grid m n
update-grid g =
  -- tabulate λ i → tabulate λ j → 
  for i yield
  for j yield
      let loc = i , j
          cell = lookup-grid loc g
      in update' cell (neighbor-count loc g)
