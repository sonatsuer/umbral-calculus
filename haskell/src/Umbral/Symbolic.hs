-- | The moment model with symbolic moments.
--
-- The scalars are integer polynomials in moment symbols @a1, a2, ...@, one
-- family per umbra, so an expression evaluates to a formula. The same
-- expression runs unchanged in the numerical model: that is what it means for
-- it to have a polymorphic type.
module Umbral.Symbolic
  ( Sym (..),
    Formula,
    symbolic,
    symbolicSimilar,
    showFormula,
  )
where

import Algebra.Polynomial
import Control.Monad.Fresh
import Data.Text (Text)
import Data.Text qualified as T
import Umbral.Language
import Umbral.Moment
import Umbral.Name

-- | The moment symbol @Sym n i@, printed as the name followed by the index.
data Sym = Sym Char Natural
  deriving (Eq, Ord)

-- | A formula in the moment symbols, with integer coefficients.
type Formula = Poly Sym Integer

-- | Each umbra @n@ has the symbolic moments @n1, n2, ...@.
symbolic :: Umbral Fresh Formula (Name Char Formula) (Poly (Name Char Formula) Formula)
symbolic = momentModel $ \n i -> var (Sym n i)

-- | Every umbra has the moments of the umbra @a@: all umbrae are similar.
symbolicSimilar :: Umbral Fresh Formula (Name Char Formula) (Poly (Name Char Formula) Formula)
symbolicSimilar = momentModel $ \_ i -> var (Sym 'a' i)

-- | Print a formula.
showFormula :: Formula -> Text
showFormula = render $ \(Sym n i) -> T.pack (n : show i)
