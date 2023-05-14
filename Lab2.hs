{-# LANGUAGE GADTs #-}

--         ∞
-- fix f = ⊔ fⁱ ⊥
--        i=0
fix :: (a -> a) -> a
fix f = f (fix f)

type Iden = String
type Σ = Iden -> Int

update :: Σ -> Iden -> Int -> Σ
update σ v n v' = if v == v' then n else σ v'

eInicial, eIniTest :: Σ
eInicial _ = undefined
eIniTest _ = 0

{- Ω ≈ (Σ' + Z × Ω + Z → Ω)⊥ -}
data Ω = Normal Σ | Abort Σ | Out (Int, Ω) | In (Int -> Ω)
{- Notar:
   * Normal : Σ → Ω
   * Abort  : Σ → Ω
   * Out    : (Z, Ω) → Ω
   * In     : (Z → Ω) → Ω
-}

data Expr a where
  -- Expresiones enteras
  Const  :: Int       -> Expr Int                      -- n
  Var    :: String    -> Expr Int                      -- v
  Plus   :: Expr Int  -> Expr Int -> Expr Int          -- e + e'
  -- e - e'
  -- e * e'
  -- e / e'
  -- Expresiones booleanas
  Eq     :: Expr Int  -> Expr Int -> Expr Bool         -- e = e'
  -- e /= e'
  -- e < e'
  -- e <= e'
  -- Comandos
  Skip   :: Expr Ω                                     -- skip
  -- newvar v := e in e'
  -- v := e
  -- fail
  -- catch c with c'
  -- while b do c
  -- if b then c else c'
  -- c ; c'
  -- !e
  -- ?v

class DomSem dom where
  sem :: Expr dom -> Σ -> dom

instance DomSem Int where
  sem (Const a)    _ = a
  sem (Var v)      σ = σ v
  sem (Plus e1 e2) σ = sem e1 σ + sem e2 σ

instance DomSem Bool where
  sem (Eq e1 e2) σ = sem e1 σ == sem e2 σ

(*.) :: (Σ -> Ω) -> Ω -> Ω
(*.) f (Normal σ)  = f σ
(*.) _ (Abort σ)   = Abort σ
(*.) f (Out (n,ω)) = Out (n, f *. ω)
(*.) f (In g)      = In ((f *.) . g)

(†.) :: (Σ -> Σ) -> Ω -> Ω
(†.) f (Normal σ)  = Normal $ f σ
(†.) f (Abort σ)   = Abort $ f σ
(†.) f (Out (n,ω)) = Out (n, f †. ω)
(†.) f (In g)      = In ((f †.) . g)

(+.) :: (Σ -> Ω) -> Ω -> Ω
(+.) _ (Normal σ)  = Normal σ
(+.) f (Abort σ)   = f σ
(+.) f (Out (n,ω)) = Out (n, f +. ω)
(+.) f (In g)      = In ((f +.) . g)

instance DomSem Ω where
  sem Skip σ = Normal σ

{- ################# Funciones de evaluación de dom ################# -}

class Eval dom where
  eval :: Expr dom -> Σ -> IO ()

instance Eval Int where
  eval e = print . sem e

instance Eval Bool where
  eval e = print . sem e

instance Eval Ω where
  eval e = unrollOmega . sem e
    where unrollOmega :: Ω -> IO ()
          unrollOmega (Normal σ)   = return ()
          unrollOmega (Abort σ)    = putStrLn "Abort"
          unrollOmega (Out (n, ω)) = print n >> unrollOmega ω
          unrollOmega (In f)       = getLine >>= unrollOmega . f . read
