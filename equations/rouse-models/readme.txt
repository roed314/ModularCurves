This collection of code computes models for modular curves. It relies on the following files:

gl2.m, gl2.sig, gl2data.m - Magma code written by Drew Sutherland with lots of functionality for subgroups of GL_2

GL2Operations.m, modcurve.m - Magma code written by David Zywina for computing spaces of modular forms and models of modular curves by multiplying weight 1 Eisenstein series.

model.m - Magma code written by Jeremy Rouse that computes a model of a modular curve as a cover of a previously computed modular curve (or "1.1.0.1" for the j-line).

finescript.m - Magma code written by Jeremy Rouse that computes the model of a "quadratic refinement".

magm_gl2zhat.txt - List of subgroups of GL_2(Z/NZ). Each entry is a tuple consisting of (i) the label of the subgroup, (ii) the subgroup itself, and (iii) labels of the parent subgroups. 
