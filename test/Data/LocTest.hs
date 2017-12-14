import Data.Loc

import Test.Hspec
import Test.QuickCheck

instance Arbitrary Loc where
  arbitrary =
    oneof
      [ Loc <$> arbitrary
      , LocPair <$> arbitrary <*> arbitrary
      , pure Initial
      , pure Terminal
      ]

main :: IO ()
main = hspec $
  describe "locations" $ do
    it "ordering should be transitive" (property prop_ord_trans)
    it "ordering should be reflexive" (property prop_ord_refl)
    it "ordering should be totlal" (property prop_ord_total)

prop_ord_trans :: Loc -> Loc -> Loc -> Bool
prop_ord_trans l1 l2 l3 = not (l1 <= l2 && l2 <= l3) || (l1 <= l3)

prop_ord_refl :: Loc -> Loc -> Bool
prop_ord_refl l1 l2 = (l1 /= l2) || (l1 <= l2 && l2 <= l1)

prop_ord_total :: Loc -> Loc -> Bool
prop_ord_total l1 l2 = l1 == l2 || l1 < l2 || l2 < l1
