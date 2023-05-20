-- Lab 2 - Lenguajes y compiladores 2023
-- Alumno: Julian Merida Renny

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
  -- n
  Const  :: Int       -> Expr Int
  -- v
  Var    :: String    -> Expr Int
   -- e + e'
  Plus   :: Expr Int  -> Expr Int -> Expr Int
  -- e - e'
  Dif   :: Expr Int -> Expr Int -> Expr Int
  -- e * e'
  Times :: Expr Int -> Expr Int -> Expr Int
  -- e / e' (división entera)
  Div   :: Expr Int -> Expr Int -> Expr Int
  -- Si e' evalúa a 0, hagan lo que quieran --> devuelve 0.

  -- Expresiones booleanas
  -- e = e'
  Eq     :: Expr Int  -> Expr Int -> Expr Bool
  -- e /= e'
  Neq  :: Expr Int  -> Expr Int -> Expr Bool
  -- e < e'
  Less :: Expr Int  -> Expr Int -> Expr Bool
  -- b && b'
  And  :: Expr Bool -> Expr Bool -> Expr Bool
  -- b || b'
  Or   :: Expr Bool -> Expr Bool -> Expr Bool
  -- ¬b
  Not  :: Expr Bool              -> Expr Bool

  -- Comandos
  -- skip
  Skip   :: Expr Ω
  -- NEWVAR v := e IN c
  Newvar  :: Iden      -> Expr Int -> Expr Ω -> Expr Ω
  -- v := e
  Assign :: Iden      -> Expr Int           -> Expr Ω
  -- FAIL
  Fail   ::                                    Expr Ω
  -- CATCHIN c WITH c'
  Catch  :: Expr Ω    -> Expr Ω             -> Expr Ω
  -- WHILE b DO c
  While  :: Expr Bool -> Expr Ω             -> Expr Ω
  -- IF b THEN c ELSE c'
  If     :: Expr Bool -> Expr Ω   -> Expr Ω -> Expr Ω
  -- c ; c'
  Seq    :: Expr Ω    -> Expr Ω             -> Expr Ω
  -- !e
  Output    :: Expr Int                      -> Expr Ω
  -- ?v
  Input    :: Iden                            -> Expr Ω

class DomSem dom where
  sem :: Expr dom -> Σ -> dom

instance DomSem Int where
  sem (Const a)    _ = a
  sem (Var v)      σ = σ v
  sem (Plus e1 e2) σ = sem e1 σ + sem e2 σ
  sem (Dif e1 e2) σ = sem e1 σ - sem e2 σ
  sem (Times e1 e2) σ = sem e1 σ * sem e2 σ
  sem (Div e1 e2) σ | sem e2 σ  /= 0 = div (sem e1 σ) (sem e2 σ)
                    | otherwise = 0

instance DomSem Bool where
  sem (Eq e1 e2) σ = sem e1 σ == sem e2 σ
  sem (Neq e1 e2) σ = sem e1 σ /= sem e2 σ
  sem (Less e1 e2) σ = sem e1 σ < sem e2 σ
  sem (And e1 e2) σ = sem e1 σ && sem e2 σ
  sem (Or e1 e2) σ = sem e1 σ || sem e2 σ
  sem (Not e1) σ = not (sem e1 σ)

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
  sem Fail s = Abort s
  sem (Assign v e) s  = Normal (update s v (sem e s))
  sem (Newvar v e c) s = (†.) (\s' -> update s' v (s v)) (sem c (update s v (sem e s)))
  sem (While b c) s = fix f s
                          where
                            f w s' | sem b s' = (*.) w (sem c s')
                                   | otherwise = Normal s'

  sem (If b c1 c2) s | sem b s = sem c1 s
                     | otherwise = sem c2 s

  sem (Catch c0 c1) s = (+.) (sem c1) (sem c0 s)
  sem (Seq c0 c1) s = (*.) (sem c1) (sem c0 s)
  sem (Input c0) s = In (\v -> Normal (update s c0 v ))
  sem (Output c0) s = Out(sem c0 s, Normal s)


-- ################# Funciones de evaluación de dom ################# --

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



-- ===============================================================================
-- Implementaciones de test propias
-- ===============================================================================

-- Ejemplo 1
-- Output

prog1 :: Expr Ω
prog1 = Seq
          (Assign "x" (Const 10))
          (Output (Var "x"))

test1 :: IO ()
test1 = eval prog1 eIniTest

-- Ejemplo 2
-- Input

prog2 :: Expr Ω
prog2 = Seq
          (Input "x")
          (Output (Var "x"))

test2 :: IO ()
test2 = eval prog2 eIniTest

-- Ejemplo 3
-- Input y While

prog3 :: Expr Ω
prog3 =
        Seq
          (Seq
            (Input "x")
            (While (Less (Var "x") (Const 10))
                    (Assign "x" (Plus (Const 1) (Var "x")))
            )
          )
          (Output (Var "x"))

test3 :: IO ()
test3 = eval prog3 eIniTest

-- Ejemplo 4
-- progDivMod with input and output

prog4 :: Expr Ω
prog4 =
  Seq
  (Seq (Input "x" )
       (Input  "y")
  )
  (
    Seq
      (If
        (Or
          (Or (Less (Var "y") (Const 0)) (Eq (Var "y") (Const 0)))
          (Less (Var "x") (Const 0))
        )
        Fail
        (Newvar "q" (Const 0)
          (Newvar "r" (Var "x")
            (Seq
              (Seq
                (While
                  (Not (Less (Var "r") (Var "y")))
                  (Seq
                    (Assign "q" (Plus (Var "q") (Const 1)))
                    (Assign "r" (Dif (Var "r") (Var "y")))
                  )
                )
                (Assign "x" (Var "q"))
              )
              (Assign "y" (Var "r"))
            )
          )
        )
      )
      (Seq
        (Output (Var "x"))
        (Output (Var "y"))
        ))

{- Ejecuta el programa de división entera a/b con a en "x" y b en "y". Devuelve
	el cociente en "x" y el resto en "y".
    Si "x" < 0 o "y" <= 0, aborta dejando los valores iniciales de "x" e "y".
-}


test4 :: IO ()
test4 = eval prog4 eIniTest


-- Ejemplo 5
-- Newvar with output

prog5 :: Expr Ω
prog5 = Seq
          (Input "x")
          (Seq
            (Newvar "x" (Const 13)
            (Seq
              (Output (Var "x"))
              (Seq
                (Assign "x" (Plus (Const 1) (Var "x")))
                (Output (Var "x"))
              )
            )
            )
            (Output (Var "x"))
          )

test5 :: IO ()
test5 = eval prog5 eIniTest