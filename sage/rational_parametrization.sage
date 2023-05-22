import pdb

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

def finite_field_morphism(domain, codomain, domain_min_poly = None, base_morphism = None):
    """
    compute a homomorhpism from domain to codomain.
    It doesn't seem to be implemented for Quotion polynomail fields
    in sage.
    """
    #we define the polynomial ring on the co-domain, in this way we can resolve
    #the minimal polynomial of the domain generator in the codomain and find
    #its image
    codomainX.<X> = PolynomialRing(codomain)
    if (not domain_min_poly):
        domain_min_poly = domain.gen().minpoly()
    #TODO: Sage doesn't know how to codomainX(domain_min_poly)
    # we should apply base_morphism to each coefficient and multiply with X^i in codomainX
    domain_min_poly_in_codomain_X = None
    if base_morphism:
        domain_min_poly_in_codomain_X = sum([base_morphism(domain_min_poly.coefficients(sparse=false)[i])*X^i for i in range(domain_min_poly.degree()+1)])
    else:
        domain_min_poly_in_codomain_X = codomainX(domain_min_poly)
        
    domain_gen_in_codomain = domain_min_poly_in_codomain_X.roots()[0][0]
    return domain.hom([domain_gen_in_codomain], base_map=base_morphism)

def generate_field_tower_quadratic_cubic_quadratic(q, quad_nr1 = None, cub_nr = None, quad_nr2=None):
    """
    returns the desired Fq2, Fq6, Fq12
    quad_nr1 is a quadratic nonresidue over Fq
    cub_nr1 is a cubic nonresidue over Fq2 represented as coefficient of {1, sqrt{quad_nr1}} basis
    quad_nr2 is a quadratic nonresidue over Fq6 represented as coefficient of {1, root3(cub_nr), root3(cub_nr)²}
    """
    FqX.<X> = PolynomialRing(FiniteField(q))#, implementation="NTL")
    
    qsqrt = q ^ 2
    qsqrt_modulus = None
    if (quad_nr1):
        qsqrt_modulus = X^2-quad_nr1

    Fqsqrt.<a> = FiniteField(qsqrt, modulus=qsqrt_modulus)
    #Then we embed our desirable generators in this field
    FqsqrtX.<X> = PolynomialRing(Fqsqrt)

    bcube = (cub_nr == None) and cubic_non_residue(Fqsqrt) or cub_nr[0] + cub_nr[1]*a

    # vvvv This didn't work because the basefield is not Fqsqrt vvvv⎈
    #####################################################################################################
    # # we are going to make the intermediary extension because we need the minimal polynomials over Fq #
    # bgen = (X^3 - bcube).roots()[0][0]                                                                #
    # cgen = (X^2 - csquare).roots()[0][0]                                                              #
    #                                                                                                   #
    # Fqsqrt3.<b> = FiniteField(qsqrt, bgen.minpoly())                                                  #
    # Fqsqrt2.<c> = FiniteField(qsqrt, cgen.minpoly())                                                  #
    #                                                                                                   #
    # Fqsqrt6.<d> = FiniteField(qsqrt^6, modulus = (bgen+cgen).minpoly())                               #
    #####################################################################################################

    #we need to define the minpoly over the base field otherwise the
    #second extension use some random minpoly instead of X^2 - csquare
    #also only polynomial over base field can be coerce to the sage
    # favorite finite field, which we need to do to compute the morphisms
    cubic_min_poly = X^3 - bcube

    # instead  of simply making the extension by degree, we are explicitly specifiying
    # the minimal polynomial
    Fqsqrt3_cubic.<b> = Fqsqrt.extension(cubic_min_poly)

    #using a quadratic non-resideu over F(q^2)³ to extend Fq^2^6 simplify
    #the norm equation
    Fqsqrt3X.<X> = PolynomialRing(Fqsqrt3_cubic)

    csquare = (quad_nr2 == None) and quadratic_non_residue(Fqsqrt) or quad_nr2[0]+ quad_nr2[1]*b + quad_nr2[2]*b**2

    quadratic_min_poly = X**2 - csquare
    Fqsqrt6_sqrt.<c> = Fqsqrt3_cubic.extension(quadratic_min_poly)

    return Fqsqrt, Fqsqrt3_cubic, Fqsqrt6_sqrt, quadratic_min_poly

def algebraic_torus_rational_parametrization(q, Fq2, Fq6, Fq12, Fq12_over_Fq6_quadratic_min_poly):
    qsqrt = q ^ 2
    Fqsqrt.<a> = Fq2
    Fqsqrt3_cubic = Fq6
    Fqsqrt6_sqrt = Fq12

    #First we create the field superfield using sage default.
    Fqsqrt6.<c> = Fqsqrt.extension(6)

    Fqsqrt3.<b1> = Fqsqrt.extension(3)

    Fqsqrt3_cubic_as_FF = finite_field_morphism(Fqsqrt3_cubic, Fqsqrt3)
    FF_to_Fqsqrt3_cubic = finite_field_morphism(Fqsqrt3, Fqsqrt3_cubic)

    Fqsqrt6.<c1> = Fqsqrt3.extension(2)

    # sage can't coerce polynomial defined over Fqsqrt6_sqrt[X] with coefficient in Fqsqrt
    # (indeed that was the whole problem which forced us to define the morpshism explicitly)
    # so we need to provide the minimal polynomial in Fqsqrt explicitly
    quadratic_min_poly = Fq12_over_Fq6_quadratic_min_poly
    Fqsqrt6_sqrt_as_FF = finite_field_morphism(Fqsqrt6_sqrt, Fqsqrt6, domain_min_poly = quadratic_min_poly, base_morphism=Fqsqrt3_cubic_as_FF)
    FF_to_Fqsqrt6_sqrt = finite_field_morphism(Fqsqrt6, Fqsqrt6_sqrt, base_morphism=FF_to_Fqsqrt3_cubic)

    A3.<u1,u2,u3> = PolynomialRing(Fqsqrt6_sqrt, 3)

    sigma2 = Fqsqrt6_sqrt.frobenius_endomorphism(4)
    sigma4 = Fqsqrt6_sqrt.frobenius_endomorphism(8)

    sigma3 = Fqsqrt6_sqrt.frobenius_endomorphism(6)

    def sigma3_in_FF():
      return Fqsqrt6_sqrt_as_FF * sigma3 * FF_to_Fqsqrt6_sqrt

    sigma2_ext = A3.hom([u1,u2,u3], codomain=A3, base_map=sigma2)
    sigma4_ext = A3.hom([u1,u2,u3], codomain=A3, base_map=sigma4)
    sigma3_ext = A3.hom([u1,u2,u3], codomain=A3, base_map=sigma3)

    A3_over_Fqsqrt3.<u1,u2,u3> = PolynomialRing(Fqsqrt3_cubic, 3)

    sigma2_cubic = Fqsqrt3_cubic.frobenius_endomorphism(4)
    sigma4_cubic = Fqsqrt3_cubic.frobenius_endomorphism(8)

    sigma2_cubic_ext = A3_over_Fqsqrt3.hom([u1,u2,u3], codomain=A3_over_Fqsqrt3, base_map=sigma2_cubic)
    sigma4_cubic_ext = A3_over_Fqsqrt3.hom([u1,u2,u3], codomain=A3_over_Fqsqrt3, base_map=sigma4_cubic)

    extend_A3_base = A3_over_Fqsqrt3.hom([u1,u2,u3], codomain=A3)

    # see: https://hackmd.io/pqLq5-MBSNGGjX-A6PFWBw
    #normal_basis = [b^2+b+1, sigma2(b^2+b+1), sigma4(b^2+b+1)]
    (b,) = Fqsqrt3_cubic._first_ngens(1)
    normal_basis_gen = b^2+b+1
    #normal_basis_gen = b
    #normal_basis = [b^2+b+1, sigma2(b^2+b+1), sigma4(b^2+b+1)]
    normal_basis = [normal_basis_gen, normal_basis_gen^(qsqrt), normal_basis_gen^(qsqrt^2)]
    #verifying Al's argument in https://hackmd.io/pqLq5-MBSNGGjX-A6PFWBw
    normal_basis_FF = [Fqsqrt3_cubic_as_FF(normal_basis_elm) for normal_basis_elm in normal_basis]
    #this step fails with ZeroDivisionError: input matrix must be nonsingular if it is not a basis
    V, From_V, To_V = Fqsqrt3.vector_space(base=Fqsqrt, map=True, basis=normal_basis_FF)
    assert(V.dimension() == 3)
    assert(V.are_linearly_dependent(normal_basis)==False)
    #check linear independence to make sure we have hit a normal basis.

    #represent gamma as a generic element in normal basis
    gamma = u1*normal_basis_gen + (sigma2_cubic(normal_basis_gen))*u2 + (sigma4_cubic(normal_basis_gen))*u3
    #gamma = u1*normal_basis_FF[0] + (normal_basis_FF[1])*u2 + (normal_basis_FF[2])*u3

    #hilbert 90 theorem says every element of normF6/F3 is of this form
    #xi = (gamma + c)/(gamma + sigma3(c))
    xi = (extend_A3_base(gamma) + FF_to_Fqsqrt6_sqrt(c1))/(extend_A3_base(gamma) + sigma3(FF_to_Fqsqrt6_sqrt(c1)))

    #our problem here was that that this passes
    # a == (gamma(1,1,1) - 55)/92
    # but this fail to coerce
    # Fqsqrt(gamma(1,1,1))
    # Hence we map gamma Fsqrt6_sqrt -> Fsqrt6 where such a coercion is possible. 

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
    A2xt = A2xt.fraction_field()
    A2xt_FF.<tf,vf1,vf2> = PolynomialRing(Fqsqrt6, 3)
    A2xt_FF = A2xt_FF.fraction_field()

    A2xt_FF.hom([t,v1,v2], codomain=A2xt, base_map=FF_to_Fqsqrt6_sqrt)

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
    FF_to_Fqsqrt6_sqrt_ext = A2xt_FF.hom([t,v1,v2], codomain=A2xt, base_map=FF_to_Fqsqrt6_sqrt)

    gamma_in_FF = Fqsqrt6_sqrt_as_FF_ext(gamma)

    #and finally the point on the torus
    torus_point_in_F6_in_v1v2 = (gamma_in_FF + Fqsqrt6_sqrt_as_FF(c))/(gamma_in_FF + Fqsqrt6_sqrt_as_FF(sigma3(c)))
    torus_point_back_in_F6_sqrt_in_v1v2 = FF_to_Fqsqrt6_sqrt_ext(torus_point_in_F6_in_v1v2)
    torus_point_in_F6_sqrt_in_v1v2 = (gamma + FF_to_Fqsqrt6_sqrt(c1))/(gamma + sigma3(FF_to_Fqsqrt6_sqrt(c1)))

    return torus_point_back_in_F6_sqrt_in_v1v2

def convert_ark_big_int_to_int(big_int_array):
    result = 0
    for i in range(0,len(big_int_array)):
        result += big_int_array[i]*(2**(64*i));

    return result

if __name__ == '__main__':
    #q = 127
    #print(algebraic_torus_rational_parametrization(127))
    q_30bit = 2147483647
    q101 = 101
    

    #bls12_381
    q = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab 
    q_ark = convert_ark_big_int_to_int([0xb9feffffffffaaab,
                                        0x1eabfffeb153ffff,
                                        0x6730d2a0f6b0f624,
                                        0x64774b84f38512bf,
                                        0x4b1ba7b6434bacd7,
                                        0x1a0111ea397fe69a])
    assert(q == q_ark)

    #bls12_377
    q = convert_ark_big_int_to_int([0x8508c00000000001,
                                    0x170b5d4430000000,
                                    0x1ef3622fba094800,
                                    0x1a22d9f300f5138f,
                                    0xc63b05c06ca1493b,
                                    0x1ae3a4617c510ea,])
    

    nonresidue_quadratic_fq =  convert_ark_big_int_to_int(
        [0xfc0b8000000002fa,
        0x97d39cf6e000018b,
        0x2072420fbfa05044,
        0xcbbcbd50d97c3802,
        0xbaf1ec35813f9eb,
        0x9974a2c0945ad2,
        ])
        
    nonresidue_cubic_fq2 =  [0, convert_ark_big_int_to_int(
       [
        202099033278250856,
        5854854902718660529,
        11492539364873682930,
        8885205928937022213,
        5545221690922665192,
        39800542322357402,
        ])]


    #nonresidue_quadratic_fq6 = cubic_root(nonresidue_cubic_fq2)
    nonresidue_quadratic_fq6 = [0, 1, 0];

    #Fq2, Fq6, Fq12 = generate_field_tower_quadratic_cubic_quadratic(q, nonresidue_quadratic_fq, nonresidue_cubic_fq2, nonresidue_quadratic_fq6)
    Fq2, Fq6, Fq12, Fq12_over_Fq6_quadratic_min_poly = generate_field_tower_quadratic_cubic_quadratic(q101)
    torus_param = algebraic_torus_rational_parametrization(q, Fq2, Fq6, Fq12, Fq12_over_Fq6_quadratic_min_poly)
    print(torus_param)
