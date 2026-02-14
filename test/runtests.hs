import Test.Tasty (defaultMain, localOption, mkTimeout, testGroup, TestTree)
import qualified Generic.TestAlgebra as A
import qualified Generic.TestTerm as ST
import qualified Set.TestTerm as T
import qualified Set.TestAlgebra as SA

tests :: TestTree
tests = testGroup "All tests" $ A.tests ++ SA.tests ++ T.tests ++ ST.tests

main :: IO ()
main = defaultMain $ localOption (mkTimeout 3000000) tests
