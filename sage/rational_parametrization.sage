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

def algebraic_torus_rational_parametrization(q, Fq2 = None, Fq6 = None, Fq12 = None, Fq12_over_Fq6_quadratic_min_poly = None):
    """
    Given a finite field F_q and its deg 12 extension F_q12, it generates
    a rational parametrization of its algebraic torus over F_q2xF_q2

    If any of extension fields are not given they are replaced with
    the generic one generated by sage
    
    """
    qsqrt = q ^ 2
    #Fqsqrt = Fq2 and Fq2 or FiniteField(qsqrt)
    #Fqsqrt3_cubic = Fq6 and Fq6 or Fqsqrt.extension(3)
    #Fqsqrt6_quad = Fq12 and Fq12 or Fqsqrt3_cubic.extension(2)
    Fqsqrt = Fq2 and Fq2 or FiniteField(qsqrt)
    Fqsqrt2_quad = FiniteField(qsqrt**2)
    Fqsqrt3_cubic = Fq6 and Fq6 or FiniteField(qsqrt^3)
    Fqsqrt6_quad = Fq12 and Fq12 or FiniteField(qsqrt^6)
    # generic sage extension are always over prime fields so we have to be explicit.
    Fqsqrt6_quad_over_cubic = Fqsqrt6_quad.over(Fqsqrt3_cubic)
    Fqsqrt3_cubic_over_Fqsqrt = Fqsqrt3_cubic.over(Fqsqrt)
    
    a  = Fqsqrt.gen()
    b  = Fqsqrt3_cubic.gen()
    c  = Fqsqrt6_quad.gen()    

    #First we create+ the field superfield using sage default.
    #Fqsqrt6.<c> = Fqsqrt.extension(6) # do we need this?

    #Fqsqrt3.<b1> = Fqsqrt.extension(3)

    #Fqsqrt3_cubic_as_FF = finite_field_morphism(Fqsqrt3_cubic, Fqsqrt3)
    #FF_to_Fqsqrt3_cubic = finite_field_morphism(Fqsqrt3, Fqsqrt3_cubic)

    #Fqsqrt6.<c1> = Fqsqrt3.extension(2)

    # sage can't coerce polynomial defined over Fqsqrt6_quad[X] with coefficient in Fqsqrt
    # (indeed that was the whole problem which forced us to define the morpshism explicitly)
    # so we need to provide the minimal polynomial in Fqsqrt explicitly
    #quadratic_min_poly = Fq12_over_Fq6_quadratic_min_poly and Fq12_over_Fq6_quadratic_min_poly or c.minimal_polynomial()
    #Fqsqrt6_quad_as_FF = finite_field_morphism(Fqsqrt6_quad, Fqsqrt6, domain_min_poly = quadratic_min_poly, base_morphism=Fqsqrt3_cubic_as_FF)
    #FF_to_Fqsqrt6_quad = finite_field_morphism(Fqsqrt6, Fqsqrt6_quad, base_morphism=FF_to_Fqsqrt3_cubic)

    A3.<u1e,u2e,u3e> = PolynomialRing(Fqsqrt6_quad, 3)

    sigma2 = Fqsqrt6_quad.frobenius_endomorphism(4)
    sigma4 = Fqsqrt6_quad.frobenius_endomorphism(8)
    sigma3 = Fqsqrt6_quad.frobenius_endomorphism(6)

    #def sigma3_in_FF():
    #  return Fqsqrt6_quad_as_FF * sigma3 * FF_to_Fqsqrt6_quad

    sigma2_ext = A3.hom([u1e,u2e,u3e], codomain=A3, base_map=sigma2)
    sigma4_ext = A3.hom([u1e,u2e,u3e], codomain=A3, base_map=sigma4)
    sigma3_ext = A3.hom([u1e,u2e,u3e], codomain=A3, base_map=sigma3)

    A3_over_Fqsqrt3.<u1,u2,u3> = PolynomialRing(Fqsqrt3_cubic, 3)
    
    sigma1_cubic = Fqsqrt3_cubic.frobenius_endomorphism(2)
    sigma2_cubic = Fqsqrt3_cubic.frobenius_endomorphism(4)

    pdb.set_trace()
    sigma1_cubic_ext = A3_over_Fqsqrt3.hom([u1,u2,u3], codomain=A3_over_Fqsqrt3, base_map=sigma1_cubic)
    sigma2_cubic_ext = A3_over_Fqsqrt3.hom([u1,u2,u3], codomain=A3_over_Fqsqrt3, base_map=sigma2_cubic)

    extend_A3_base = A3_over_Fqsqrt3.hom([u1,u2,u3], codomain=A3)

    # see: https://hackmd.io/pqLq5-MBSNGGjX-A6PFWBw
    #normal_basis = [b^2+b+1, sigma2(b^2+b+1), sigma4(b^2+b+1)]
    pdb.set_trace()
    b = Fqsqrt3_cubic.over(Fqsqrt).gen()
    normal_basis_gen = b^2 + b + 1
    #first we try to use b to generate normal basis
    normal_basis = [normal_basis_gen, normal_basis_gen^(qsqrt), normal_basis_gen^(qsqrt^2)]
    try:
        V, From_V, To_V = Fqsqrt3_cubic.vector_space(base=Fqsqrt, map=True, basis=normal_basis)

    except ValueError:
        cubic_residue = b
        try:
            b_cube_root = cubic_residue.nth_root(3)
        except ValueError:
            cubic_residue = b^3
        
        normal_basis_gen = cubic_residue^2+cubic_residue+1

    # Now we have found the normal_basis_gen we can map it back to the default field
    normal_basis_gen = Fqsqrt3_cubic(normal_basis_gen)
    #normal_basis_gen = b
    #normal_basis = [b^2+b+1, sigma2(b^2+b+1), sigma4(b^2+b+1)]
    normal_basis = [normal_basis_gen, normal_basis_gen^(qsqrt), normal_basis_gen^(qsqrt^2)]
    #verifying Al's argument in https://hackmd.io/pqLq5-MBSNGGjX-A6PFWBw
    #normal_basis_FF = [Fqsqrt3_cubic_as_FF(normal_basis_elm) for normal_basis_elm in normal_basis]
    #this step fails with ZeroDivisionError: input matrix must be nonsingular if it is not a basis
    #check linear independence to make sure we have hit a normal basis.
    pdb.set_trace()
    try:
        V, From_V, To_V = Fqsqrt3_cubic.vector_space(base=Fqsqrt, map=True, basis=normal_basis)
        assert(V.dimension() == 3)
        assert(V.are_linearly_dependent(normal_basis)==False)
    except NotImplementedError:
        # if we can't too bad
        pass

    #represent gamma as a generic element in normal basis
    gamma = u1*normal_basis_gen + (sigma1_cubic(normal_basis_gen))*u2 + (sigma2_cubic(normal_basis_gen))*u3
    #gamma = u1*normal_basis_FF[0] + (normal_basis_FF[1])*u2 + (normal_basis_FF[2])*u3

    #hilbert 90 theorem says every element of normF6/F3 is of this form
    #xi = (gamma + c)/(gamma + sigma3(c))
    xi = (extend_A3_base(gamma) + c)/(extend_A3_base(gamma) + sigma3(c))

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

    # just for testing that our norms are correct
    def norm_F6_over_F(elm):
        return elm * sigma4_ext(sigma3_ext(elm)) * sigma2_ext(elm)  * sigma3_ext(elm) * sigma4_ext(elm) * sigma2_ext(sigma3_ext(elm))

    #    return elm * Fqsqrt6.frobenius_endomorphism(4)(elm) * Fqsqrt6.frobenius_endomorphism(8)(elm)

    # xi.num/x.denom = 1 (the last denom is to tell sage that the element is in the polynomial ring not
    # the field of fraction.
    Ugen1 = ((norm_F6_over_F2(xi.numerator())) - norm_F6_over_F2(xi.denominator())).numerator()
    Ugen2 =  norm_F6_over_F2(extend_A3_base(gamma) + c) - norm_F6_over_F2(extend_A3_base(gamma) + sigma3(c))

    # We actually need to generate Ugen using a square root x such that Fq(x) = Fq^2(x)
    pdb.set_trace()
    found_non_residue = False
    non_residue = 0
    while(not(found_non_residue)):
        non_residue = Fqsqrt.random_element()
        if not non_residue.is_square() == False:
            found_non_residue = True

    assert(Fqsqrt2_quad(non_residue).is_square())
    Ugen2 = (sigma_ext(gamma)*sigma2_ext(gamma)+
    
    #we make new affine space for new variable names
    A2xt.<t,v1,v2> = PolynomialRing(Fqsqrt6_quad, 3)
    A2xt = A2xt.fraction_field()
    
    def project_hypersurface_on_to_affine_plane(Ugen):
        #Note that the Ugen is a multivariate polynomial over Fq12
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

        #the plane equation tangent at point (V1[0]['u1'], V1[0]['u2'], V1[0]['u3']) is 
        #u1 = V1[0]['u1']
        a_point = (V_tangent[0]['u1e'], V_tangent[0]['u2e'], V_tangent[0]['u3e'])

        #intersecting V_tangent with the U to find the tangent point a
        #a_finder = Ugen.subs({u1:u1, w2: V1[0]['u2'], w3: V1[0]['u3']})
        #a_point = [a_finder.roots()[0][0], V1[0]['w2'], V1[0]['w3']]
        assert(Ugen.subs({u1e: a_point[0], u2e: a_point[1], u3e: a_point[2]})== 0)

        #A2xt_FF.<tf,vf1,vf2> = PolynomialRing(Fqsqrt6, 3)
        #A2xt_FF = A2xt_FF.fraction_field()

        #A2xt_FF.hom([t,v1,v2], codomain=A2xt, base_map=FF_to_Fqsqrt6_quad)

        pdb.set_trace()
        #cross the line from a0 to (a0 + (1, v1, v2)) with U   
        line_cross_U = Ugen.subs({u1e: a_point[0] + t, u2e:  a_point[1] + t*v1, u3e: a_point[2] + t*v2})
        #here we just dividing by t because we know a0 is a ponit on U
        assert(line_cross_U.subs({t : 0}) == 0)
        torus_t = (line_cross_U/t).numerator()

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

        print("t in v1,v2: ", t_in_v1_v2.subs({t:1, v1: 1, v2:1}))


        #then you can subsitute for v1,v2 and t and get u1, u2 and u3 which you can subs
        u1_in_v1v2 =  a_point[0] + t_in_v1_v2
        u2_in_v1v2 =  a_point[1] + t_in_v1_v2*v1
        u3_in_v1v2 =  a_point[2] + t_in_v1_v2*v2

        return (u1_in_v1v2, u2_in_v1v2, u3_in_v1v2)

    pdb.set_trace()
    u_in_v1v2 = project_hypersurface_on_to_affine_plane(Ugen)
    #which gives you a gamma in v1 v2
    sigma1_cubic_in_Fqsqrt6 = Fqsqrt6_quad.frobenius_endomorphism(2)
    sigma2_cubic_in_Fqsqrt6 = Fqsqrt6_quad.frobenius_endomorphism(4)
    sigma1_cubic_ext_to_v1v2 = A2xt.hom([t,v1,v2], codomain=A2xt, base_map=sigma1_cubic_in_Fqsqrt6)
    sigma2_cubic_ext_to_v1v2 = A2xt.hom([t,v1,v2], codomain=A2xt, base_map=sigma4_cubic_in_Fqsqrt6)

    pdb.set_trace()
    gamma = u_in_v1v2[0]*normal_basis_gen + (sigma1_cubic_ext_to_v1v2(normal_basis_gen))*u_in_v1v2[1] + (sigma2_cubic_ext_to_v1v2(normal_basis_gen))*u_in_v1v2[2]

    #Fqsqrt6_quad_as_FF_ext = A2xt.hom([tf,vf1,vf2], codomain=A2xt_FF, base_map=Fqsqrt6_quad_as_FF)
    #FF_to_Fqsqrt6_quad_ext = A2xt_FF.hom([t,v1,v2], codomain=A2xt, base_map=FF_to_Fqsqrt6_quad)

    #gamma_in_FF = Fqsqrt6_quad_as_FF_ext(gamma)

    #and finally the point on the torus
    #torus_point_in_F6_in_v1v2 = (gamma_in_FF + Fqsqrt6_quad_as_FF(c))/(gamma_in_FF + Fqsqrt6_quad_as_FF(sigma3(c)))
    #torus_point_back_in_F6_sqrt_in_v1v2 = FF_to_Fqsqrt6_quad_ext(torus_point_in_F6_in_v1v2)
    torus_point_in_F6_sqrt_in_v1v2 = (gamma + c)/(gamma + sigma3(c))
    
    def rho_u(torus_element):
        pdb.set_trace()
        assert(norm_F6_over_F(torus_element) == 1), "given element is not on the torus"
        beta = Fqsqrt6_quad_over_cubic(torus_element).vector()
        gamma = (1 + beta[0])/beta[1]
        assert((gamma + c)/(gamma + sigma3(c)) == torus_element)
        du_in_poly_basis = Fqsqrt3_cubic_over_Fqsqrt(gamma)
        du = in_terms_of_normal_basis(du_in_poly_basis, normal_basis_gen)
        assert(Ugen.subs({u1e: du[0],u2e: du[1],u3e: du[2]}) == 0)
        #check the inverse being correct
        new_gamma = sum([du[i]*(normal_basis_gen)^(qsqrt^i) for i in range(3)])
        assert((new_gamma + c)/(new_gamma + sigma3(c)) == torus_element)
        return  du
        
    def rho(torus_element):
        pdb.set_trace()
        assert(torus_element.norm() == 1), "given element is not on the torus"
        beta = Fqsqrt6_quad_over_cubic(torus_element).vector()
        du_in_poly_basis = Fqsqrt3_cubic_over_Fqsqrt((1 + beta[0])/beta[1])
        du = in_terms_of_normal_basis(du_in_poly_basis, normal_basis_gen)
        assert(sum([du[i]*normal_basis[i] for i in range(Fqsqrt3_cubic_over_Fqsqrt.degree_over())])==du_in_poly_basis)
        return ((du[1] - a_point[1])/(du[0] - a_point[0]), (du[2] - a_point[2])/(du[0]-a_point[0]))

    pdb.set_trace()
    te = c**((13**12 - 1)/cyclotomic_polynomial(12)(13))
    te_u = rho_u(te)
    #Now we compute the inverse map.(1+beta1)/b2
    #torus_projection_to_v1v2 = Fsqrt6_sqrt.hom([
    random_torus_element = torus_point_in_F6_sqrt_in_v1v2.subs({t:1, v1: 1, v2: 1})
    re_on_V = rho(random_torus_element)

    print(random_torus_element)
    print(torus_point_in_F6_sqrt_in_v1v2.subs({t:1, v1: re_on_V[0], v2: re_on_V[1]}))
    assert(random_torus_element == torus_point_in_F6_sqrt_in_v1v2.subs({t:1, v1: re_on_V[0], v2: re_on_V[1]}))
    
    return torus_point_in_F6_sqrt_in_v1v2

def convert_ark_big_int_to_int(big_int_array):
    result = 0
    for i in range(0,len(big_int_array)):
        result += big_int_array[i]*(2**(64*i));

    return result

def in_terms_of_normal_basis(element_to_convert, normal_basis_gen):
    parent_field = element_to_convert.parent()
    base_field = element_to_convert.base_ring()
    base_field_size = base_field.order()
    normal_basis = [(normal_basis_gen)^(base_field_size^i) for i in range(parent_field.degree(base_field))]
    print(normal_basis)
    V, From_V, To_V = parent_field.vector_space(base=base_field, map=True, basis=normal_basis)
    #W = [to_V(b) for b in normal_basis]
    #if (V.span(W).dimension() != V.dimension):
    #    raise ValueError("the given generator does not results in a normal basis")

    #W0 = V.span_of_basis(W)
    return To_V(element_to_convert)

# sage: k.<a> = GF(2^5)
# sage: k
# Finite Field in a of size 2^5
# sage: V = k.vector_space()
# sage: z = (1+a)^17; z
# a^3 + a + 1
# sage: def to_V(w):
# ...       return V(w.polynomial().padded_list(V.dimension()))
# sage: to_V(z)
# (1, 1, 0, 1, 0)
# sage: B2 = [(a+1)^(2^i) for i in range(k.degree())]
# sage: W = [to_V(b) for b in B2]
# sage: V.span(W).dimension()
# 5
# sage: W0 = V.span_of_basis(W)
# sage: def in_terms_of_normal_basis(z):
# ...       return W0.coordinates(to_V(z))
# sage: in_terms_of_normal_basis(a+1)
# [1, 0, 0, 0, 0]
# sage: in_terms_of_normal_basis(1 + a + a^2 + a^3)
# [1, 0, 0, 1, 0]

if __name__ == '__main__':
    #q = 127
    #print(algebraic_torus_rational_parametrization(127))
    q_30bit = 2147483647
    q101 = 101    
    
    #bls12_381
    #0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

    q381 = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
    q377 = 0x01ae3a4617c510eac63b05c06ca1493b1a22d9f300f5138f1ef3622fba094800170b5d44300000008508c00000000001
    
    q_ark = convert_ark_big_int_to_int([0xb9feffffffffaaab,
                                        0x1eabfffeb153ffff,
                                        0x6730d2a0f6b0f624,
                                        0x64774b84f38512bf,
                                        0x4b1ba7b6434bacd7,
                                        0x1a0111ea397fe69a])
    assert(q381 == q_ark)

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
    #Fq2, Fq6, Fq12, quad_min = generate_field_tower_quadratic_cubic_quadratic(q101)
    #torus_param = algebraic_torus_rational_parametrization(q101, Fq2, Fq6, Fq12, quad_min)
    torus_param = algebraic_torus_rational_parametrization(13)
    torus_param = algebraic_torus_rational_parametrization(101)
    # torus_param = algebraic_torus_rational_parametrization(q101)
    
    # print(torus_param)
    # #torus_param = algebraic_torus_rational_parametrization(q)
    # #print(torus_param)
    # Fq2, Fq6, Fq12, Fq12_over_Fq6_quadratic_min_poly = generate_field_tower_quadratic_cubic_quadratic(q101)
    # torus_param = algebraic_torus_rational_parametrization(q101, Fq2, Fq6, Fq12, Fq12_over_Fq6_quadratic_min_poly)
    
    # print(torus_param)
