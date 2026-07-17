import Xlib.CharDegrees
import Xlib.BCGPUBarrier
import Xlib.CUCapacity
import Proofs.BilinearComplexity.Omega
import Proofs.BilinearComplexity.GroupTensor

-- CharDegrees pillar theorems
#print axioms Xlib.CharDegrees.charDegreeSum_two
#print axioms Xlib.CharDegrees.card_charDegrees
#print axioms Xlib.CharDegrees.charDegrees_eq_of_algEquiv

-- BilinearComplexity pillar theorems
#print axioms BilinearComplexity.rank_matMulTensor_le_of_isTPP
#print axioms BilinearComplexity.two_le_omega
#print axioms BilinearComplexity.omega_le_three
#print axioms BilinearComplexity.omega_lt_three

-- CUCapacity pillar theorem
#print axioms Xlib.CUCapacity.two_lt_pseudoExponent

-- BCGPUBarrier theorems
#print axioms Xlib.BCGPUBarrier.bcgpu_thm_3_2
#print axioms Xlib.BCGPUBarrier.bcgpu_cor_3_3
#print axioms Xlib.BCGPUBarrier.bcgpu_cor_3_4_kernel
#print axioms Xlib.BCGPUBarrier.bcgpu_cor_3_5
#print axioms Xlib.BCGPUBarrier.bcgpu_thm_3_6
#print axioms Xlib.BCGPUBarrier.bcgpu_cor_3_8
