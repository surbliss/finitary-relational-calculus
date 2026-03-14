import Dict.Tests qualified
import Test.Tasty (TestTree, defaultMain, localOption, mkTimeout, testGroup)

tests :: TestTree
tests =
  testGroup "All tests" $
    [ Dict.Tests.tests
    ]

main :: IO ()
main = defaultMain $ localOption (mkTimeout 30000000) tests
