#q = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab #bls12_381
#q = 2147483647 
q = 127
qsqrt = q ^ 2
Fqsqrt.<a> = FiniteField(qsqrt)
Fqsqrt3.<b> = Fqsqrt.extension(3)
Fqsqrt6.<c> = Fqsqrt3.extension(2)

A3.<u1,u2,u3> = PolynomialRing(Fqsqrt6, 3)

sigma2 = Fqsqrt6.frobenius_endomorphism(4)
sigma4 = Fqsqrt6.frobenius_endomorphism(8)

sigma3 = Fqsqrt6.frobenius_endomorphism(6)

sigma2_ext = A3.hom([u1,u2,u3], codomain=A3, base_map=sigma2)
sigma4_ext = A3.hom([u1,u2,u3], codomain=A3, base_map=sigma4)

normal_basis = [b,b^(q),b^(q^2)]
V, From_V, To_V = Fqsqrt3.vector_space(base=Fqsqrt, map=True, basis=normal_basis)
assert(V.dimension() == 3)
assert(V.are_linearly_dependent(normal_basis)==False)
#check linear independence to make sure we have hit a normal basis.

#represent gamma as a generic element in normal basis
gamma = u1*b + (sigma2_ext(b))*u2 + (sigma4_ext(b))*u3

#hilbert 90 theorem says every element of normF6/F3 is of this form
xi = (gamma + c)/(gamma + sigma3(c))
                                       
def norm_F6_over_F2(elm):
    return elm * sigma2_ext(elm) * sigma4_ext(elm)
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
A2xt.<t,v1,v2> = PolynomialRing(Fqsqrt6, 3)

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

gamma = u1_in_v1v2*b + (sigma2_ext(b))*u2_in_v1v2 + (sigma4_ext(b))*u3_in_v1v2

#and finally the point on the torus
torus_point_in_F6_in_v1v2 = (gamma + c)/(gamma + sigma3(c))

