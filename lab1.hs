{-# LANGUAGE GADTs #-}

--         ∞
-- fix f = ⊔ fⁱ ⊥
--        i=0
fix :: (a -> a) -> a
fix f = f (fix f) -- A kind of magic!

type Iden = String

type Σ = Iden -> Int

-- Alias por si escribir Σ les resulta complicado
type State = Σ

-- Función de actualización de estado
update :: Σ -> Iden -> Int -> Σ
update σ v n v' =
  if v == v'
    then n
    else σ v'

{- Para probar con eval: usen al principio eIniTest que no rompe nada si quieren
    saber cuánto termina valiendo una variable  -}

eInicial, eIniTest :: Σ
eInicial = \_ -> undefined
eIniTest = \_ -> 0

{- Ω ≈ Σ + Σ -}
data Ω
  = Normal Σ
  | Abort Σ

{- Notar:
   * Normal : Σ → Ω
   * Abort  : Σ → Ω
   -}

-- Alias por si escribir Ω les resulta complicado
type Omega = Ω

data Expr a where
  {- Expresiones enteras -}

  -- n
  Const :: Int                  -> Expr Int
  -- v
  Var   :: Iden                 -> Expr Int
  -- e + e'
  Plus  :: Expr Int -> Expr Int -> Expr Int
  -- e - e'
  Dif   :: Expr Int -> Expr Int -> Expr Int
  -- e * e'
  Times :: Expr Int -> Expr Int -> Expr Int
  -- e / e' (división entera)
  Div   :: Expr Int -> Expr Int -> Expr Int
  -- Si e' evalúa a 0, hagan lo que quieran.

  {- Expresiones booleanas -}

  -- e = e'
  Eq   :: Expr Int  -> Expr Int -> Expr Bool
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

  {- Comandos -}

  -- SKIP
  Skip   ::                                    Expr Ω
  -- NEWVAR v := e IN c
  Local  :: Iden      -> Expr Int -> Expr Ω -> Expr Ω
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


{- Completar las ecuaciones semánticas -}

class DomSem dom where
  sem :: Expr dom -> Σ -> dom

instance DomSem Int where
  sem (Const a) _    = a
  sem (Var v) σ      = σ v
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

{- Función de control para Ω -}

(*.) :: (Σ -> Ω) -> Ω -> Ω
(*.) f (Normal σ) = f σ
(*.) _ (Abort σ)  = Abort σ

(+.) :: (Σ -> Ω) -> Ω -> Ω
(+.) _ (Normal σ) = Normal σ
(+.) f (Abort σ)  = f σ

-- dagger
(++.) :: (Σ -> Σ) -> Ω -> Ω
(++.) f (Normal σ) = Normal (f σ)
(++.) f (Abort σ)  = Abort (f σ)

instance DomSem Ω where
  sem Skip s = Normal s
  sem Fail s = Abort s
  sem (Assign v e) s  = Normal (update s v (sem e s))
  sem (Local v e c) s = (++.) (\s' -> update s' v (s v)) ((sem c) (update s v (sem e s)))
  sem (While b c) s = fix f s
                          where
                            f w s' | sem b s' = (*.) w (sem c s')
                                   | otherwise = Normal s

  sem (If b c1 c2) s | sem b s = sem c1 s
                     | otherwise = sem c2 s

  sem (Catch c0 c1) s = (+.) (sem c1) (sem c0 s)
  sem (Seq c1 c2) s = (*.) (sem c2) (sem c1 s)

{- ################# Funciones de evaluación de dom ################# -}
class Eval dom where
  eval :: [Iden] -> Expr dom -> Σ -> IO ()

instance Eval Int where
  eval _ e = print . sem e

instance Eval Bool where
  eval _ e = print . sem e

instance Eval Ω where
  eval lvars e = \sigma -> mapM_ (f (elsigma (sem e sigma))) lvars
    where
      elsigma (Normal σ) = σ
      elsigma (Abort σ)  = σ
      f s var = putStrLn (var ++ " vale " ++ (show (s var)))

-- Ejemplo 1
{- Usen esto con eInicial o eIniTest pasando una lista de variables -}
prog1 :: Expr Ω
prog1 = Assign "x" (Const 8)

ejemplo1 :: IO ()
ejemplo1 = eval ["x"] prog1 eIniTest

{- Debe devolver 4 en "x" y 5 en "y" -}

-- Ejemplo 2
prog2 :: Expr Ω
prog2 = Seq
          (Seq
            (Assign "x" (Const 3))
            (Assign "y" (Const 5))
          )
          (Assign "x"
            (Div (Plus (Var "x") (Var "y")) (Const 2))
          )

ejemplo2 :: IO ()
ejemplo2 = eval ["x", "y"] prog2 eInicial

{- Este programa debe comportarse como Skip -}

-- Ejemplo 3
prog3 :: Expr Ω
prog3 =
  Catch
    (Local "x" (Const 7) Fail)
    Skip

ejemplo3 :: IO ()
ejemplo3 = eval ["x"] prog3 eIniTest

{- División y Resto -}

-- Ejemplo 4
progDivMod :: Expr Ω
progDivMod =
  If
    (Or
      (Or (Less (Var "y") (Const 0)) (Eq (Var "y") (Const 0)))
      (Less (Var "x") (Const 0))
    )
    Fail
    (Local "q" (Const 0)
      (Local "r" (Var "x")
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

{- Ejecuta el programa de división entera a/b con a en "x" y b en "y". Devuelve
	el cociente en "x" y el resto en "y".
    Si "x" < 0 o "y" <= 0, aborta dejando los valores iniciales de "x" e "y".
-}

ejemploDivMod :: Int -> Int -> IO ()
ejemploDivMod a b = eval ["x", "y"] progDivMod $
  update (update eInicial "x" a) "y" b

-- Fin de funciones del enunciado


-- Implementaciones de test propias
--
--
--
-- Assignations
program1 :: Expr Ω
program1 = Seq
            (Assign "x" (Const 10))
            (Assign "y" (Const 20))

test1 :: IO ()
test1 = eval ["x", "y", "c"] program1 (eIniTest)

-- Conditional
program2 :: Expr Ω
program2 = Seq
          (Assign "c" (Const 3 ))
          ( If ( Eq (Var "x") (Var "y"))
              (Assign "c" (Const 1) )
              ( Assign "c" (Const 2) )
          )

test2 :: Int -> Int -> Int -> IO ()
test2 a b c = eval ["x", "y", "c"] program2 $
              (update (update (update eIniTest "x" a) "y" b) "c" c)

-- While
program3 :: Expr Ω
program3 = While
            ( Less (Var "x") (Const 10) )
            ( Assign "x"
              ( Plus (Var "x") (Const 1) )
            )


test3 :: Int -> IO ()
test3 a = eval ["x"] program3 $
      (update eIniTest "x" a)

-- Newvar
program4 :: Expr Ω
program4 = Local "x" (Const 3) Skip

test4 :: IO ()
test4 = eval ["x"] program4 eIniTest

-- Catch
-- x deberia ser 36
program5a :: Expr Ω
program5a = Seq (Catch Fail Skip) (Assign "x" (Const 36))

test5a :: IO ()
test5a = eval ["x"] program5a eIniTest

-- x deberia ser 36 porque Asign asigna siempre aunque falle
program5b :: Expr Ω
program5b = Seq (Catch Skip Fail) (Assign "x" (Const 36))

test5b :: IO ()
test5b = eval ["x"] program5b eIniTest

-- Div by 0
program6 :: Expr Int
program6 = Div (Const 3) (Const 0)


test6 :: IO ()
test6 = eval ["x"] program6 eIniTest

-- Nuevo While. Esta bien que no cambie el valor dentro del while?
program7 :: Expr Ω
program7 = Seq
              (Seq
                (Assign "x" (Const 3))
                ( While
                    ( Less (Var "x") (Const 10) )
                    ( Assign "x" (Plus (Var "x") (Const 1)) )
                )
              )
              (Assign "x" (
                Plus (Var "x") (Const 1) )
              )


test7 :: IO ()
test7 = eval ["x"] program7 eInicial


-- Division
test8 :: Int
test8 = sem (Div (Const 11) (Const 5)) (eInicial)

-- Plus
test9 :: Int
test9 = sem (Plus (Const 15) (Const 13)) eInicial

test10 :: Int
test10 = sem (Plus (Const 15) (Const (-18))) eInicial


-- Dif
test11 :: Int
test11 = sem (Dif (Const 15) (Const (-18))) eInicial

-- Times
test12 :: Int
test12 = sem (Times (Const 15) (Const (3))) eInicial

-- Bools
-- equal

my_true :: Expr Bool
my_true = Eq (Const 1) (Const 1)

my_false :: Expr Bool
my_false = Not(my_true)

test13 :: Bool
test13 = sem (And (my_true) (my_true)) eInicial

test14 :: Bool
test14 = sem (Or (my_true) (my_true)) eInicial

test15 :: Bool
test15 = sem (And (my_false) (my_true)) eInicial

test16 :: Bool
test16 = sem (Or (my_false) (my_true)) eInicial