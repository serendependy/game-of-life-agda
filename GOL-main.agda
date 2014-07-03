open import Prelude
open import Text.Lex

open import Game-of-Life

module GOL-main where

-- IO stuff
showCell : Cell → String
showCell alive = "◼"
showCell dead  = "◻"

showGrid : ∀ {m n} → Grid m n → String
showGrid g = 
  vfold (λ _ → String)
        (λ row str → str & "\n" & 
           vfold (λ _ → String) (λ c str' → showCell c & str') "" row) "" g

-- Show instances
ShowCell : Show Cell
ShowCell = simpleShowInstance showCell

ShowGrid : ∀ {m n} → Show (Grid m n)
ShowGrid = simpleShowInstance showGrid

run : ∀ {m n} → Grid m n → Nat → IO Unit 
run g zero = putStrLn (show g)
run g (suc n) = putStrLn (show g)
            >>= λ _ → run (update-grid g) n

module ParseGOL where
  eqCell : (c₁ c₂ : Cell) → Dec (c₁ ≡ c₂)
  eqCell alive alive = yes refl
  eqCell alive dead  = no (λ ())
  eqCell dead  alive = no (λ ())
  eqCell dead  dead  = yes refl

  EqCellToken : Eq Cell
  EqCellToken = record { _==_ = eqCell }

  cellTok : Cell → String → TokenDFA Char (Maybe Cell)
  cellTok c s = just c <$ keywordToken (unpackString s)

  cellTokenSpecs : List (TokenDFA Char (Maybe Cell))
  cellTokenSpecs = 
      cellTok alive "1"
    ∷ cellTok dead  "0"
    ∷ (nothing <$ matchToken isSpace)
    ∷ []

  lex : String → List Cell
  lex = concatMap (maybe [] [_]) ∘ tokenize cellTokenSpecs ∘ unpackString

private
  liftM : ∀ {a} {A : Set a} → Maybe A → String → Either String A
  liftM nothing  str = left str
  liftM (just x) str = right x

  liftD : ∀ {a} {A : Set a} → Dec A → String → Either String A
  liftD (yes x) _   = right x
  liftD (no  _) str = left str


readGOLFile : String → Either String (Σ Nat SqGrid)
readGOLFile s = case lines s of
  λ { [] → left "Nothing in file!" 
    ; (l ∷ ls') → liftM (parseNat l) "Invalid number"
      >>= λ n → liftD (length ls' == n) "rows ≠ header"
      >>= λ eq → right (listToVec ls') 
      >>= λ vstr → strToVecEither n (vmap ParseGOL.lex vstr) 
      >>= λ g → return (n , subst (λ n' → Grid n' n) (length ls') n eq g) }
  where
    strToVecEither : ∀ {m} n → Vec (List Cell) m → Either String (Grid m n)
    strToVecEither n [] = right []
    strToVecEither {suc m} n (xs ∷ vstr) =
        liftD (length xs == n) "Length of rows ≠ header"
      >>= λ eq  → right (listToVec xs) 
      >>= λ vxs → strToVecEither n vstr 
      >>= λ g   → return ((subst (Vec Cell) (length xs) n eq vxs) ∷ g)


checkGOLArgs : String → String → Either String (Nat × (Σ Nat SqGrid))
checkGOLArgs stepsTxt file =
      liftM (parseNat stepsTxt) "STEPS must be valid!" 
  >>= λ steps → readGOLFile file 
  >>= λ { (n , g) → return (steps , (n , g)) }


main : IO Unit
main = getArgs >>= 
  λ { (file ∷ [ stepsTxt ]) → readFile file 
       >>= λ ftext → case checkGOLArgs stepsTxt ftext of 
       λ { (left err) → putStrLn err
         ; (right (steps , dim , grid)) → run grid steps }
  ; _ → getProgName 
    >>= λ p → putStrLn ("Usage: " & p & "FILE STEPS") }