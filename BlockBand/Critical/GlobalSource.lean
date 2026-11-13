module

public import BlockBand.Critical.GlobalSource.Statement
public import BlockBand.Critical.GlobalSource.Uniqueness
public import BlockBand.Critical.GlobalSource.Measurability
public import BlockBand.Critical.GlobalSource.Assembly
public import BlockBand.Critical.GlobalSource.Bridge
public import BlockBand.Critical.GlobalSource.SourceSequences
public import BlockBand.Critical.GlobalSource.Tightness
public import BlockBand.Critical.GlobalSource.CharTests
public import BlockBand.Critical.GlobalSource.Sampling
public import BlockBand.Critical.GlobalSource.Closing
public import BlockBand.Critical.GlobalSource.Replacement
public import BlockBand.Critical.GlobalSource.BlockLaws
public import BlockBand.Critical.GlobalSource.Rescaling
public import BlockBand.Critical.GlobalSource.GapC
public import BlockBand.Critical.GlobalSource.ReplacementProof

/-!
# The global Gaussian source lemma

This file collects the global Gaussian source lemma: the finite-width probe matrices
`(𝒦_W, B_W)` of the ring path, the statement `GlobalGaussianSourceStatement` and the
uniqueness of its limit object, and its proof by sampling the probe tags, a Lindeberg
replacement of sampled tags by Gaussian probes, and tightness from the source moments.
-/
