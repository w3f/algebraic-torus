# finding a quadratic non-residue by brute force
def quadratic_non_residue (basefield):
    basefield_x.<X> = PolynomialRing(basefield)
    for i in basefield:
        potential_minpoly = X^2 - i
        if potential_minpoly.is_irreducible():
            return i

def cubic_non_residue (basefield):
    basefield_x.<X> = PolynomialRing(basefield)
    for i in basefield:
        potential_minpoly = X^3 - i
        if potential_minpoly.is_irreducible():
            return i

def non_cubic_irreducible_element(basefield):
    while(true) :
        test_element = FqsqrtX.irreducible_element(3)
        if test_element.monomial_coefficient(X) != 0:
            return test_element
        
#q = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab #bls12_381
#q = 2147483647 
q = 127
qsqrt = q ^ 2
Fqsqrt.<a> = FiniteField(qsqrt)

#First we create the field superfield using sage default.
Fqsqrt6.<c> = Fqsqrt.extension(6)

#Then we embed our desirable generators in this field
FqsqrtX.<X> = PolynomialRing(Fqsqrt)

csquare = quadratic_non_residue(Fqsqrt)
bcube = cubic_non_residue(Fqsqrt)

# vvvv This didn't work because the basefield is not Fqsqrt vvvv
# we are going to make the intermediary extension because we need the minimal polynomials over Fq
#bgen = (X^3 - bcube).roots()[0][0]
#cgen = (X^2 - csquare).roots()[0][0]

# Fqsqrt3.<b> = FiniteField(qsqrt, bgen.minpoly())
# Fqsqrt2.<c> = FiniteField(qsqrt, cgen.minpoly())

# Fqsqrt6.<d> = FiniteField(qsqrt^6, modulus = (bgen+cgen).minpoly())

FqsqrtX.<X> = PolynomialRing(Fqsqrt)

#we need to define the minpoly over the base field otherwise the
#second extension use some random minpoly instead of X^2 - csquare
#so we store them so we can abuse X later
cubic_min_poly = X^3 - bcube
quadratic_min_poly = X^2 - csquare

# instead  of simply making the extension by degree, we are explicitly specifiying
# the minimal polynomial
Fqsqrt3_cubic.<b> = Fqsqrt.extension(cubic_min_poly)
Fqsqrt3.<b1> = Fqsqrt.extension(3)

# redefining the poly ring to able to solve the minpoly
# to find the image of the generator in sage favorite version of
# F_q^12
# Fqsqrt3X.<X> = PolynomialRing(Fqsqrt3)

FqsqrtX.<X> = PolynomialRing(Fqsqrt3)
bgen = (X^3 - bcube).roots()[0][0]
Fqsqrt3_cubic_as_FF = Hom(Fqsqrt3_cubic, Fqsqrt3)([bgen])
# mid_hom  = 

# mid_hom  = Hom(Fqsqrt3_cubic, Fqsqrt3)([bgen])

#using a quadratic non-resideu over Fq^2 to extend Fq^2^6 simplify
#the norm equation
Fqsqrt6_sqrt.<c> = Fqsqrt3_cubic.extension(quadratic_min_poly)
Fqsqrt6.<c1> = Fqsqrt3.extension(2)

Fqsqrt6X.<X> = PolynomialRing(Fqsqrt6)

# bgen = Fqsqrt6X(cubic_min_poly).roots()[0][0]

# mid_hom  = Fqsqrt3_cubic.hom([bgen])

cgen = Fqsqrt6X(quadratic_min_poly).roots()[0][0]
Fqsqrt6_sqrt_as_FF = Fqsqrt6_sqrt.hom([cgen], base_map=Fqsqrt3_cubic_as_FF)
Fqsqrt6_to_sqrt = Fqsqrt6_sqrt_as_FF.inverse_image

A3.<u1,u2,u3> = PolynomialRing(Fqsqrt6_sqrt, 3)

sigma2 = Fqsqrt6_sqrt.frobenius_endomorphism(4)
sigma4 = Fqsqrt6_sqrt.frobenius_endomorphism(8)

sigma3 = Fqsqrt6_sqrt.frobenius_endomorphism(6)

def sigma3_in_FF(ff_elm):
  return Fqsqrt6_sqrt_as_FF(sigma3(Fqsqrt6_sqrt_as_FF.inverse_image(ff_elm)))

sigma2_ext = A3.hom([u1,u2,u3], codomain=A3, base_map=sigma2)
sigma4_ext = A3.hom([u1,u2,u3], codomain=A3, base_map=sigma4)
sigma3_ext = A3.hom([u1,u2,u3], codomain=A3, base_map=sigma3)

# see: https://hackmd.io/pqLq5-MBSNGGjX-A6PFWBw
#normal_basis = [b^2+b+1, sigma2(b^2+b+1), sigma4(b^2+b+1)]
normal_basis_gen = b^2+b+1
#normal_basis_gen = b
#normal_basis = [b^2+b+1, sigma2(b^2+b+1), sigma4(b^2+b+1)]
normal_basis = [normal_basis_gen, normal_basis_gen^(qsqrt), normal_basis_gen^(qsqrt^2)]
#verifying Al's arg in https://hackmd.io/pqLq5-MBSNGGjX-A6PFWBw
normal_basis_FF = [Fqsqrt3_cubic_as_FF(normal_basis_elm) for normal_basis_elm in normal_basis]
#this step fails with ZeroDivisionError: input matrix must be nonsingular if it is not a basis
V, From_V, To_V = Fqsqrt3.vector_space(base=Fqsqrt, map=True, basis=normal_basis_FF)
assert(V.dimension() == 3)
assert(V.are_linearly_dependent(normal_basis)==False)
#check linear independence to make sure we have hit a normal basis.

#represent gamma as a generic element in normal basis
gamma = u1*normal_basis_gen + (sigma2(normal_basis_gen))*u2 + (sigma4(normal_basis_gen))*u3

#f = FiniteFieldHomomorphism_generic(Hom(parent(a), parent(gamma(1,1,1)))); f
#hilbert 90 theorem says every element of normF6/F3 is of this form
xi = (gamma + c)/(gamma + sigma3(c))

#our problem here is that this passes
# a == (gamma(1,1,1) - 55)/92
# but this fail to coerce
# Fqsqrt(gamma(1,1,1))
# TODO: find a way to map a in Fsqrt6 to a in Fqsrt

def norm_F6_over_F2(elm):
    return elm * sigma2_ext(elm) * sigma4_ext(elm)

# just for testing hilbert 90
def norm_F6_over_F3(elm):
    return elm * sigma3_ext(elm)

#    return elm * Fqsqrt6.frobenius_endomorphism(4)(elm) * Fqsqrt6.frobenius_endomorphism(8)(elm)

# xi.num/x.denom = 1 (the last denom is to tell sage that the element is in the polynomial ring not
# the field of fraction.
Ugen = ((norm_F6_over_F2(xi.numerator())) - norm_F6_over_F2(xi.denominator())).numerator()

# make sure U is a surface by checking the dimension
U = A3.ideal([Ugen])
assert(U.dimension() == 2)

# Finding a tangent plane with nice coordinates 
Uhs = AffineHypersurface(Ugen)
M = Uhs.Jacobian_matrix()
#ideal contatining the gradiant of all plane tangent an U at various points but parallel to xy plane
#chose one (randomly) with setting first coordinate = 1
plane_ideal_norm_100 = Ideal(Ugen, M[0][1], M[0][2])
V_tangent = plane_ideal_norm_100.variety()

#the plane equation tangent at point (V1[0]['u2'], V1[0]['u2'], V1[0]['u3']) is 
#u1 = V1[0]['u1']
a_point = (V_tangent[0]['u1'], V_tangent[0]['u2'], V_tangent[0]['u3'])

#intersecting V_tangent with the U to find the tangent point a
#a_finder = Ugen.subs({u1:u1, w2: V1[0]['u2'], w3: V1[0]['u3']})
#a_point = [a_finder.roots()[0][0], V1[0]['w2'], V1[0]['w3']]
assert(Ugen.subs({u1: a_point[0], u2: a_point[1], u3: a_point[2]})== 0)

#we make new affine space for new variable names
A2xt.<t,v1,v2> = PolynomialRing(Fqsqrt6_sqrt, 3)
A2xt_FF.<tf,vf1,vf2> = PolynomialRing(Fqsqrt6, 3)

#cross the line from a to (a0 + (1, v1, v2)) with U   
line_at_u = Ugen.subs({u1: a_point[0] + t, u2:  a_point[1] + t*v1, u3: a_point[2] + t*v2})
#here we just dividing by t because we know a0 is a ponit on U
torus_t = (line_at_u/t).numerator()

#this gives you a degree 1 equation for t, to eleminate t and hence
#parametrizing the torus only with v1 and v2
#we solve it for t manually as I couldn't find a way to ask Sage to do it

t_in_v1_v2_num = 0
t_in_v1_v2_denom = 0 
for i in range(0, len(torus_t.monomials())):
    assert(torus_t.monomials()[i].degree(t) <= 1)
    if torus_t.monomials()[i].degree(t) == 0:
        t_in_v1_v2_num -= torus_t.coefficients()[i] * torus_t.monomials()[i]
    else:
        t_in_v1_v2_denom += torus_t.coefficients()[i] * (torus_t.monomials()[i]/t)

#so you can subsitute for v1 and v2 and get t.
t_in_v1_v2 =  t_in_v1_v2_num / t_in_v1_v2_denom

#then you can subsitute for v1,v2 and t and get u1, u2 and u3 which you can subs
u1_in_v1v2 =  a_point[0] + t_in_v1_v2
u2_in_v1v2 =  a_point[1] + t_in_v1_v2*v1
u3_in_v1v2 =  a_point[2] + t_in_v1_v2*v2

#which gives you a gamma in v1 v2
sigma2_ext = A2xt.hom([t,v1,v2], codomain=A2xt, base_map=sigma2)
sigma4_ext = A2xt.hom([t,v1,v2], codomain=A2xt, base_map=sigma4)

gamma = u1_in_v1v2*normal_basis_gen + (sigma2_ext(normal_basis_gen))*u2_in_v1v2 + (sigma4_ext(normal_basis_gen))*u3_in_v1v2

Fqsqrt6_sqrt_as_FF_ext = A2xt.hom([tf,vf1,vf2], codomain=A2xt_FF, base_map=Fqsqrt6_sqrt_as_FF)
gamma_in_FF = Fqsqrt6_sqrt_as_FF_ext(gamma.numerator())/Fqsqrt6_sqrt_as_FF_ext(gamma.denominator())
#and finally the point on the torus
torus_point_in_F6_in_v1v2 = (gamma_in_FF + Fqsqrt6_sqrt_as_FF(c))/(gamma_in_FF + Fqsqrt6_sqrt_as_FF(sigma3(c)))
torus_point_in_F6_sqrt_in_v1v2 = (gamma + c)/(gamma + sigma3(c))
