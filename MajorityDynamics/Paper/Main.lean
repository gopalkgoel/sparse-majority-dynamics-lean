import MajorityDynamics.Paper.Assembly
import MajorityDynamics.Paper.Expansion.Main

/-! The paper's main theorem, with the expansion phase proved from the actual
majority-dynamics process. Its only nonfoundational dependencies are the
explicitly accepted cited literature contracts; inspect Paper/Final/Checks. -/
namespace MajorityDynamics.Paper

/-- The original uniform fixed-coloring theorem on Fin N. -/
theorem main : MainTheorem := main_of_expansion Expansion.expansion

end MajorityDynamics.Paper
