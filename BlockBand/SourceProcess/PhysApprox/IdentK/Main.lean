module

public import BlockBand.SourceProcess.PhysApprox.IdentK.FiniteW
public import BlockBand.SourceProcess.PhysApprox.IdentK.Passage
public import BlockBand.SourceProcess.PhysApprox.IdentK.Bridge

/-!
# The `𝒦` generator identification `CapIdentKDoubleGen`

`capIdentKDoubleGen_holds` assembles three parts:
* `kFiniteW_holds : KFiniteW`: the finite-`W` tested increments vanish;
* `kFddPassage : KFddPassage`: the passage to the limit for drift-free tests;
* `kGBridge_holds : KGBridge`: `genKG = genKY + D` and `isTestedMart_ibp`.

Hence `capIdentKDouble_holds : Ident2.CapIdentKDouble`.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK

/-- **The `𝒦` generator identification `CapIdentKDoubleGen`**, from `KFiniteW`, `KFddPassage`
and `KGBridge`. -/
theorem capIdentKDoubleGen_holds : CapIdentKDoubleGen :=
  capIdentKDoubleGen_of_parts kFiniteW_holds kFddPassage kGBridge_holds

/-- **`CapIdentKDouble`**, via `capIdentKDouble_of_gen`. -/
theorem capIdentKDouble_holds : Ident2.CapIdentKDouble :=
  capIdentKDouble_of_gen capIdentKDoubleGen_holds

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK
