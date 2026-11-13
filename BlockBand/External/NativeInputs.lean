module

public import BlockBand.External.PSSS.SourceStatement
public import BlockBand.External.CEH.SourceStatement
public import BlockBand.External.ErdosRiabov.Statement
public import BlockBand.External.Johansson.SourceStatement
public import BlockBand.External.Prekopa.SourceStatement

/-!
# The cited external theorems, as one bundle of hypotheses

`NativeInputs` collects the external theorems cited by the paper. It proves none of them. Each
field is stated with the model, measure, observables and quantifiers of its source. No internal
QUE, GaussianBulk sine, Palm, coarea, regular-window, short-ring, remote Schatten,
source-process, limiting-law or endpoint conclusion is a field.

The constant of Peled–Schenker–Shamis–Sodin (PSSS) is absolute and positive, chosen before all
dimensions, deformations, intervals and orders. The Cipolloni–Erdős–Henheik (CEH) statement is
uniform in its fixed source families and polynomial classes, with the MDE, spacing and eigenpair
prerequisites explicit. The Erdős–Riabov statement is the case `k = 1` of their Theorem 3.3,
with all seven admissibility clauses. The Johansson statement is only the finite deformed
Gaussian kernel formula with `S = t/N`. The Prékopa statement is the full nonnegative
completed-Lebesgue marginal theorem.
The Benigni and BHY results are cited for context only; the complex/Palm adaptations
used in the paper are proved internally, rather than becoming extra assumed fields.

This bundle is never installed as a typeclass or axiom. It must be passed
explicitly to any theorem that uses it.
-/

set_option autoImplicit false
@[expose] public section

namespace BlockBand.External

universe u

/-- The cited external theorems, without any adaptation to the physical model. -/
structure NativeInputs where
  psss : PSSS.SourceContract.{u}
  ceh : ∀ W : CEH.WignerFamily, CEH.SourceContract W
  erdosRiabov : ErdosRiabov.SourceContract.{u}
  johansson : Johansson.SourceContract
  prekopa : Prekopa.SourceContract

/-- Packaging of the given statements into `NativeInputs`. -/
def NativeInputs.ofSources
    (psss : PSSS.SourceContract.{u})
    (ceh : ∀ W : CEH.WignerFamily, CEH.SourceContract W)
    (erdosRiabov : ErdosRiabov.SourceContract.{u})
    (johansson : Johansson.SourceContract) (prekopa : Prekopa.SourceContract) :
    NativeInputs.{u} :=
  ⟨psss, ceh, erdosRiabov, johansson, prekopa⟩

end BlockBand.External
