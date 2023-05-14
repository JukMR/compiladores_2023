-- Lab 1 - Lenguajes y compiladores 2023
-- Alumno: Julian Merida Renny

-- Contenidos de este archivo:
--
--
-- Codigo del enunciado / ecuaciones semanticas completas
-- Ejemplos / tests manuales
-- Chequeo automático de tests (resultados guardados en una variable booleana)


-- Test:
-- Se implementaron test adicionales a los provistos en el enunciado.

-- Primero se implementó versiones para probar a mano y despues se implementaron variables en
-- donde se corren estos test con valores pre cargados y se comprueba que los resultados sean los
-- esperados.

-- El resultado de todos los test se guarda en la variable `ok`. En esta variable se guarda el estado
-- `and` de todos los tests. Es decir, si ok == True entonces todos los tests pasaron correctamente.

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
eInicial _ = undefined
eIniTest _ = 0

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

-- Funcion control daga
(++.) :: (Σ -> Σ) -> Ω -> Ω
(++.) f (Normal σ) = Normal (f σ)
(++.) f (Abort σ)  = Abort (f σ)

instance DomSem Ω where
  sem Skip s = Normal s
  sem Fail s = Abort s
  sem (Assign v e) s  = Normal (update s v (sem e s))
  sem (Local v e c) s = (++.) (\s' -> update s' v (s v)) (sem c (update s v (sem e s)))
  sem (While b c) s = fix f s
                          where
                            f w s' | sem b s' = (*.) w (sem c s')
                                   | otherwise = Normal s'

  sem (If b c1 c2) s | sem b s = sem c1 s
                     | otherwise = sem c2 s

  sem (Catch c0 c1) s = (+.) (sem c1) (sem c0 s)
  sem (Seq c0 c1) s = (*.) (sem c1) (sem c0 s)

-- ################# Funciones de evaluación de dom ################# --
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
      f s var = putStrLn (var ++ " vale " ++ show (s var))

-- Ejemplo 1
{- Usen esto con eInicial o eIniTest pasando una lista de variables -}

prog1 :: Expr Ω
prog1 = Assign "x" (Const 8)

ejemplo1 :: IO ()
ejemplo1 = eval ["x"] prog1 eIniTest

-- Debe devolver 8

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

{- Debe devolver 4 en "x" y 5 en "y" -}

-- Ejemplo 3
prog3 :: Expr Ω
prog3 =
  Catch
    (Local "x" (Const 7) Fail)
    Skip

ejemplo3 :: IO ()
ejemplo3 = eval ["x"] prog3 eIniTest
{- Este programa debe comportarse como Skip -}

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

-- ===============================================================================
-- Fin de funciones del enunciado
-- ===============================================================================

-- ===============================================================================
-- Implementaciones de test propias
-- ===============================================================================

-- Ejemplo 5
-- Assignations
prog5 :: Expr Ω
prog5 = Seq
            (Assign "x" (Const 10))
            (Assign "y" (Const 20))

test5 :: IO ()
test5 = eval ["x", "y", "c"] prog1 eIniTest

-- Ejemplo 6
-- Conditional
prog6 :: Expr Ω
prog6 = Seq
          (Assign "c" (Const 3 ))
          ( If ( Eq (Var "x") (Var "y"))
              (Assign "c" (Const 1) )
              ( Assign "c" (Const 2) )
          )

test6 :: Int -> Int -> Int -> IO ()
test6 a b c = eval ["x", "y", "c"] prog6 $
              update (update (update eIniTest "x" a) "y" b) "c" c

-- Ejemplo 7
-- While
prog7 :: Expr Ω
prog7 = While
            ( Less (Var "x") (Const 10) )
            ( Assign "x"
              ( Plus (Var "x") (Const 1) )
            )


test7 :: Int -> IO ()
test7 a = eval ["x"] prog7 $
      update eIniTest "x" a

-- Ejemplo 8
-- Newvar
prog8 :: Expr Ω
prog8 = Local "x" (Const 3) Skip

test8 :: IO ()
test8 = eval ["x"] prog8 eIniTest

-- Ejemplo 9
-- Catch
-- x deberia ser 36
prog9 :: Expr Ω
prog9 = Seq (Catch Fail Skip) (Assign "x" (Const 36))

test9 :: IO ()
test9 = eval ["x"] prog9 eIniTest

-- Ejemplo 10
-- x deberia ser 36 porque Asign asigna siempre aunque falle
prog10 :: Expr Ω
prog10 = Seq (Catch Skip Fail) (Assign "x" (Const 36))

test10 :: IO ()
test10 = eval ["x"] prog10 eIniTest

-- Ejemplo 11
-- Div by 0
prog11 :: Expr Ω
prog11 = Assign "x" (Div (Const 3) (Const 0))


test11 :: IO ()
test11 = eval ["x"] prog11 eIniTest

-- Ejemplo 12
-- Nuevo While
prog12 :: Expr Ω
prog12 = Seq
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


test12 :: IO ()
test12 = eval ["x"] prog12 eInicial

-- Tests expresiones enteras

-- Ejemplo 13
-- Division
test13 :: Int
test13 = sem (Div (Const 11) (Const 5)) eInicial

-- Ejemplo 14
-- Plus
test14 :: Int
test14 = sem (Plus (Const 15) (Const 13)) eInicial

-- Ejemplo 15
test15 :: Int
test15 = sem (Plus (Const 15) (Const (-18))) eInicial

-- Ejemplo 16
-- Dif
test16 :: Int
test16 = sem (Dif (Const 15) (Const (-18))) eInicial

-- Ejemplo 17
-- Times
test17 :: Int
test17 = sem (Times (Const 15) (Const 3)) eInicial

-- Tests expresiones booleanas

myTrue :: Expr Bool
myTrue = Eq (Const 1) (Const 1)

myFalse :: Expr Bool
myFalse = Not myTrue

-- Ejemplo 18
test18 :: Bool
test18 = sem (And myTrue myTrue) eInicial

-- Ejemplo 19
test19 :: Bool
test19 = sem (Or myTrue myTrue) eInicial

-- Ejemplo 20
test20 :: Bool
test20 = sem (Not(And myFalse myTrue)) eInicial

-- Ejemplo 21
test21 :: Bool
test21 = sem (Or myFalse myTrue) eInicial


-- ===============================================================================
-- Chequeo de tests automaticos
-- ===============================================================================


-- Funcion auxiliar
getSigmaFromOmega :: Ω -> Σ
getSigmaFromOmega (Normal s) = s
getSigmaFromOmega (Abort s) = s

-- Ejemplo 1

assertProg1 :: Bool
assertProg1 = getSigmaFromOmega (sem prog1 eInicial) "x" == 8

-- Ejemplo 2

assertProg2x :: Bool
assertProg2x = getSigmaFromOmega (sem prog2 eInicial) "x" == 4

assertProg2y :: Bool
assertProg2y = getSigmaFromOmega (sem prog2 eInicial) "y" == 5

assertProg2 :: Bool
assertProg2 = and [assertProg2x,  assertProg2y]

-- Ejemplo 3

assertProg3x :: Bool
assertProg3x = getSigmaFromOmega (sem prog3 eIniTest) "x" == 0

assertProg3 :: Bool
assertProg3 = and [assertProg3x]


-- Ejemplo 4

assertEjemploDivModCheckx :: Bool
assertEjemploDivModCheckx = getSigmaFromOmega (sem progDivMod (update (update eInicial "x" 13) "y" 2) ) "x" == 6

assertEjemploDivModChecky :: Bool
assertEjemploDivModChecky = getSigmaFromOmega (sem progDivMod (update (update eInicial "x" 13) "y" 2) ) "y" == 1

assertProg4 :: Bool
assertProg4 = and [assertEjemploDivModCheckx, assertEjemploDivModChecky]

-- Ejemplo 5

assertProg5a :: Bool
assertProg5a = getSigmaFromOmega (sem prog5 eIniTest) "x" == 10

assertProg5b :: Bool
assertProg5b = getSigmaFromOmega (sem prog5 eIniTest) "y" == 20

assertProg5 :: Bool
assertProg5 = and [assertProg5a, assertProg5b]

-- Ejemplo 6

assertProg6Status :: Σ
assertProg6Status = update (update (update eIniTest "x" 25) "y" 25) "c" 10

assertProg6_1_a :: Bool
assertProg6_1_b :: Bool
assertProg6_1_c :: Bool

assertProg6_1_a = getSigmaFromOmega (sem prog6 assertProg6Status) "x" == 25
assertProg6_1_b = getSigmaFromOmega (sem prog6 assertProg6Status) "y" == 25
assertProg6_1_c = getSigmaFromOmega (sem prog6 assertProg6Status) "c" == 1

assertProg6Status2 :: Σ
assertProg6Status2 = update (update (update eIniTest "x" 13) "y" 25) "c" 10

assertProg6_2_a :: Bool
assertProg6_2_b :: Bool
assertProg6_2_c :: Bool

assertProg6_2_a = getSigmaFromOmega (sem prog6 assertProg6Status2) "x" == 13
assertProg6_2_b = getSigmaFromOmega (sem prog6 assertProg6Status2) "y" == 25
assertProg6_2_c = getSigmaFromOmega (sem prog6 assertProg6Status2) "c" == 2

assertProg6 :: Bool
assertProg6 = and [assertProg6_1_a, assertProg6_1_b, assertProg6_1_c, assertProg6_2_a, assertProg6_2_b, assertProg6_2_c]

-- Ejemplo 7

assertProg7a :: Bool
assertProg7a = getSigmaFromOmega (sem prog7 (update eIniTest "x" (-133))) "x" == 10

assertProg7b :: Bool
assertProg7b = getSigmaFromOmega (sem prog7 (update eIniTest "x" 133)) "x" == 133


assertProg7 :: Bool
assertProg7 = and [assertProg7a, assertProg7b]

-- Ejemplo 8

assertProg8a :: Bool
assertProg8a = getSigmaFromOmega (sem prog8 (update eIniTest "x" 10)) "x" == 10

assertProg8b :: Bool
assertProg8b = getSigmaFromOmega (sem prog8 eIniTest) "x" == 0


assertProg8 :: Bool
assertProg8 = and [assertProg8a, assertProg8b]

-- Ejemplo 9

assertProg9a :: Bool
assertProg9a = getSigmaFromOmega (sem prog9 (update eIniTest "x" 10)) "x" == 36

assertProg9b :: Bool
assertProg9b = getSigmaFromOmega (sem prog9 eIniTest) "x" == 36


assertProg9 :: Bool
assertProg9 = and [assertProg9a, assertProg9b]

-- Ejemplo 10

assertProg10a :: Bool
assertProg10a = getSigmaFromOmega (sem prog10 (update eIniTest "x" 10)) "x" == 36

assertProg10b :: Bool
assertProg10b = getSigmaFromOmega (sem prog10 eIniTest) "x" == 36


assertProg10 :: Bool
assertProg10 = and [assertProg10a, assertProg10b]

-- Ejemplo 11

assertProg11a :: Bool
assertProg11a = getSigmaFromOmega (sem prog11 (update eIniTest "x" 11)) "x" == 0

assertProg11 :: Bool
assertProg11 = and [assertProg11a]

-- Ejemplo 12

assertProg12a :: Bool
assertProg12a = getSigmaFromOmega (sem prog12 (update eIniTest "x" 1234)) "x" == 11

assertProg12 :: Bool
assertProg12 = and [assertProg12a]

-- Ejemplo 13

assertProg13 :: Bool
assertProg13 = test13 == 2

-- Ejemplo 14

assertProg14 :: Bool
assertProg14 = test14 == 28

-- Ejemplo 15

assertProg15 :: Bool
assertProg15 = test15 == (-3)

-- Ejemplo 16

assertProg16 :: Bool
assertProg16 = test16 == (33)

-- Ejemplo 17

assertProg17 :: Bool
assertProg17 = test17 == (45)


-- All asserts
allAserts :: Bool
allAserts = and [assertProg1, assertProg2, assertProg3,
                assertProg4, assertProg5, assertProg6,
                assertProg7, assertProg8, assertProg9,
                assertProg10, assertProg11, assertProg12,
                assertProg13, assertProg14, assertProg15,
                assertProg16, assertProg17]


-- All bools asserts
allBools :: Bool
allBools = and [test18, test19, test20, test21]

-- Final program assert
ok :: Bool
ok = allAserts && allBools
