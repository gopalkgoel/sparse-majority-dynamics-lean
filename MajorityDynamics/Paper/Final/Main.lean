import MajorityDynamics.Paper.Main
import MajorityDynamics.Paper.Final.Transport

/-! The paper's fixed-coloring and random-opinions results on arbitrary finite
vertex sets, with real densities and the original uniform quantifiers. -/
namespace MajorityDynamics.Paper
open Probability.RandomOpinionsReduction

theorem main_finite : MainFiniteTheorem := main_finite_of_main main

theorem main_finite_real : MainFiniteRealTheorem := main_finite_real_of_main main

theorem random_opinions : RandomOpinionsTheorem := random_opinions_of_main main

theorem random_opinions_finite_real : RandomOpinionsFiniteRealTheorem :=
  random_opinions_finite_real_of_main main

end MajorityDynamics.Paper
