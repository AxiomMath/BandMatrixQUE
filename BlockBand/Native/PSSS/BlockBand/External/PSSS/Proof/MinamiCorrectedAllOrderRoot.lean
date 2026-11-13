module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCorrectedUniformIntegratedSuccessor
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCorrectedRootAssembly
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.StrictPositiveInput

/-!
# All-order PSSS factorial-moment bound

The order-independent successor step is combined with the Wegner estimate (the order-one case)
before the factorial order is chosen. By induction, one positive constant bounds the falling
factorial moments of the interval eigenvalue count at every positive order, for every normalized
block-GUE law, which yields a `StrictPositivePSSSInput`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 12000000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

universe u

/-- One absolute constant proves the canonical public factorial estimate at
all positive orders.  The constant is fixed before the order, dimensions,
deterministic deformation, and closed interval. -/
theorem exists_allOrder_publicFactorialAtOrder :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ r : ℕ, 1 ≤ r → PublicFactorialAtOrder C r := by
  obtain ⟨K, hK, hsucc⟩ := exists_orderIndependent_publicFactorial_successor
  obtain ⟨CW, hCW, hwegner⟩ := wegner
  let C := max K CW
  have hKC : K ≤ C := le_max_left _ _
  have hCWC : CW ≤ C := le_max_right _ _
  have hC : 1 ≤ C := hK.trans hKC
  have hbase : PublicFactorialAtOrder C 1 :=
    (publicFactorialAtOrder_one_of_wegnerBound hwegner).mono_constant hCWC
  refine ⟨C, hC, ?_⟩
  intro r hr
  induction r with
  | zero => omega
  | succ r ih =>
      cases r with
      | zero => simpa using hbase
      | succ r =>
          exact hsucc hKC (ih (by omega))

/-- There is a `PSSSInput` with a strictly positive constant: the all-order factorial
estimate, together with integrability of the falling factorials, covers every order `r ≥ 1`
and every closed interval. -/
theorem exists_positive_psssInput :
    ∃ input : PSSSNative.BlockBand.PSSSInput.{u},
      0 < input.C := by
  obtain ⟨C, hC, hall⟩ := exists_allOrder_publicFactorialAtOrder
  let input : PSSSNative.BlockBand.PSSSInput.{u} :=
    { C := C
      C_nonneg := le_trans (by norm_num) hC
      factorialIntegrable := by
        intro k dims hd M A₀ a b r
        exact blockGUE_descFactorial_integrable hd M A₀ a b r
      factorialCount := by
        intro k dims hd M A₀ a b hab r hr
        exact (hall r hr).integral_law_le
          (le_trans (by norm_num) hC) dims hd M A₀ a b hab }
  exact ⟨input, zero_lt_one.trans_le hC⟩

/-- The PSSS factorial-count estimate holds with a strictly positive constant, for every normalized
block-GUE law. This is the external eigenvalue-count theorem. -/
theorem thm_external_count :
    Nonempty PSSSNative.BlockBand.StrictPositivePSSSInput.{u} := by
  obtain ⟨input, hinput⟩ := exists_positive_psssInput
  exact ⟨⟨input, hinput⟩⟩

/-- A chosen witness of `StrictPositivePSSSInput`. -/
noncomputable def correctedStrictPositivePSSSInput :
    PSSSNative.BlockBand.StrictPositivePSSSInput.{u} :=
  Classical.choice thm_external_count

end PSSSNative.BlockBand.PSSS
