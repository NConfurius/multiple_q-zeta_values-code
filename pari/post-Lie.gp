/* ---------- calculations ------------ */

/* (co-)product of universal enveloping algebra */

coprod_shuffle_letter({letter = v1}, {n = 1}) = {
   return(vector(n+1, i , vector(n+1, j, if(i==j, [letter],[]))));
};

coprod_shuffle_word({w = [v1,v2]}, {n = 1}) = {
    my(ret, tmp_l, tmp_ll, tmp_r, tmp_rr, ii = 1);
    if(w == [], return([vector(n+1,i,[])]));
    if(#w == 1, return(coprod_shuffle_letter(w[1],n)));
    tmp_l = coprod_shuffle_letter(w[1],n);
    tmp_r = coprod_shuffle_word(w[^1],n); 
    ret = vector(#tmp_l*#tmp_r);
    for(ll = 1, #tmp_l,
        tmp_ll = tmp_l[ll];
        for(rr = 1, #tmp_r, 
            tmp_rr = tmp_r[rr];
            ret[ii] = vector(n+1, i, vector(#tmp_ll[i]+#tmp_rr[i], j, if(j <= #tmp_ll[i], tmp_ll[i][j], tmp_rr[i][j-#tmp_ll[i]])));
            ii++;
        );
    );
    return(ret);
};

shuffle_prod({w1 = [v0,v1]}, {w2 = [v1,v0,v2]}) = {
    my(ret = [], tmp1, tmp2, tmp3);
    if(w1 == [] || w2 == [], return([concat(w1,w2)]));
    tmp1 = shuffle_prod(w1[^1], w2);
    tmp1 = vector(#tmp1, n, concat(w1[1], tmp1[n]));
    ret = concat(ret, tmp1);
    tmp2 = shuffle_prod(w1, w2[^1]);
    tmp2 = vector(#tmp2, n, concat(w2[1], tmp2[n]));
    ret = concat(ret, tmp2);
    return(ret);
};

antipode({vec = [3,1,2]}) = {
    return([(-1)^#vec, vector(#vec, i, vec[#vec+1-i])]);
};

ari_multiplicity({k = [2,3,4]}, {l = [1,1,2]}) = {
    if(#k != #l, return(0));
    return((-1)^(vecsum(k)+vecsum(l)) * prod(i = 1, #l, binomial(k[i]-1, l[i]-1)));
};

uri_multiplicity({a = 2}, {vect = [1,2,3,1]}) = {
    my(m = #vect, j = 0, tmp = 0, ind);
    m = #vect;
    if(m == 0 || a > vecsum(vect), 
        ind = 0,
        while(tmp < a, j++; tmp += vect[j]);
        ind = j;
    );
    return(1/m! * sum(k = 0, ind-1, binomial(m,k) * bernfrac(k)));
};

/* derivations */

deriv_ihara_letter({f = v2v1v0v0v1}, {g = v5}) = {
    my(f_ind, g_ind, ret = 0);
    f_ind = word_to_index(f);
    g_ind = word_to_index(g);
    if(#g_ind != 1, error("Second input must be a letter."));
    if(g_ind[1] > 0,
        ret += eval(Str("v",strjoin(concat(g_ind,f_ind),"v")));
        ret -= eval(Str("v",strjoin(concat(f_ind,g_ind),"v")));
    );
    return(ret);
};

deriv_ari_letter({f = v2v1v0v0v1}, {g = v5}) = {
    my(a, all_l, f_l, j, k, lf, lk, mult_ari, f_ind, g_ind, sum_k, tmp_l, tmp_v, ret = 0);
    f_ind = word_to_index(f);
    g_ind = word_to_index(g);
    if(#g_ind != 1, error("Second input must be a letter."));
    a = g_ind[1];
    if(a == 0, return(0));
    lf = #f_ind;
    lk = 1;
    k = vector(lf);
    for(i = 1, lf,
        if(f_ind[i] > 0, 
            k[lk] = f_ind[i];
            lk++
        );
    );
    k = k[1..lk-1]; /* non-zero entries of f_ind */
    lk = #k;
    sum_k = vecsum(k);
    all_l = generate_all_l_indices(k);
    for(i = 1, #all_l,
        tmp_l = all_l[i];
        mult_ari = ari_multiplicity(k, tmp_l);
        f_l = vector(lf);
        j = 1;
        for(ff = 1, lf,
            if(f_ind[ff] != 0, 
                f_l[ff] = all_l[i][j];
                j++
            );
        );
        tmp_v = Str("v",a+sum_k-vecsum(tmp_l));
        f_l = Str("v",strjoin(f_l,"v"));
        ret += mult_ari * eval(concat(tmp_v, f_l));
        ret -= mult_ari * eval(concat(f_l, tmp_v));
    );
    return(ret);
};

deriv_uri_letter({f = v2v1v0v0v1}, {g = v5}) = {
    my(ret, g_ind, a, lf, f_l, lk, k, sum_k, all_l, mult_ari, tmp, ll, tmp_a, tmp_l, ii, mult, rr = 1);
    f_ind = word_to_index(f);
    g_ind = word_to_index(g);
    if(#g_ind != 1, error("Second input must be a letter."));
    a = g_ind[1];
    if(a == 0, return(0));
    lf = #f_ind;
    lk = 1;
    k = vector(lf);
    for(i = 1, lf,
        if(f_ind[i] > 0,
            k[lk] = f_ind[i];
            lk++
        );
    );
    k = k[1..lk-1]; /* non-zero entries of f_ind */
    sum_k = vecsum(k);
    ret = vector(2^(a+sum_k));
    all_l = generate_all_l_indices(k);
    for(i = 1, #all_l,
        tmp_l = all_l[i];
        mult_ari = ari_multiplicity(k, tmp_l);
        f_l = vector(lf);
        ii = 1;
        for(ff = 1, lf,
            if(f_ind[ff] == 0,
                0,
                f_l[ff] = all_l[i][ii];
                ii++;
            );
        );
        tmp_a = composition(a+sum_k-vecsum(tmp_l));
        for(j = 1, #tmp_a,
            mult = mult_ari * uri_multiplicity(a, tmp_a[j]) ;
            if(mult != 0,
                ret[rr] = Ad_vec_word(tmp_a[j] , [[mult, f_l]]);
                rr++;
            );
        );
    );
    rr = rr-1;
    ret = ret[1..rr];
    tmp = vector(sum(i = 1, rr, #ret[i]));
    ll = 1;
    for(r = 1, rr,
        for(j = 1, #ret[r],
        tmp[ll] = ret[r][j];
        ll++;
        );
    );
    ret = sum(n = 1, #tmp, tmp[n][1] * eval(Str("v",strjoin(tmp[n][2],"v"))));
    return(ret);
};

deriv_word({f = v1v3}, {g = v3v1v2}, {product = ihara}) = {
    my(g_ind, d_str, tmp, tmp_g, ret = 0, var, var_ind, var_new);
    g_ind = word_to_index(g);
    product = product_name(product);
    d_str = Str("deriv_",product,"_letter");
    for(n = 1, #g_ind,
        tmp = eval(Str(d_str, "(",f,",","v",g_ind[n],")"));
        var = variables(eval(tmp));
        var_ind = eval(vector(#var, i, strsplit(Str(var[i]),"v")[^1]));
        var_new = vector(#var);
        for(j = 1, #var,
            tmp_g = g_ind;
            tmp_g[n] = var_ind[j];
            var_new[j] = concat(tmp_g);
        );
        var_new = vector(#var_new, i, eval(Str("v",strjoin(var_new[i],"v"))));
        ret += substvec(tmp, var, var_new);
    );
    return(simplify(ret));
};

deriv_poly({f = v2v0 + v1v0}, {g = v3v0v1 + v2v1}, {product = ihara}) = {
    my(var_f, coeff_f, var_g, coeff_g, ret = 0);
    product = product_name(product);
    [coeff_f, var_f] = poly_to_indexset(f);
    [coeff_g, var_g] = poly_to_indexset(g);
    for(i = 1, #var_f,
        for(j = 1, #var_g,
            ret += coeff_f[i] * coeff_g[j] * deriv_word(var_f[i], var_g[j], product);
        );
    );
    return(simplify(ret));
};

/* post-lie product conventions (cf. tr_num_to_str):
ihara:  tr_num = 0
ari:    tr_num = 1
uri:    tr_num = 2
*/

tr_0({f = 2*v0v2v3 - 4*v1v0v2}, {g = v5 + 3*v2v3}) = {
    return(deriv_poly(f,g,ihara));
};


tr_1({f = 2*v0v2v3 - 4*v1v0v2}, {g = v5 + 3*v2v3}) = {
    return(deriv_poly(f,g,ari));
};


tr_2({f = 2*v0v2v3 - 4*v1v0v2}, {g = v5 + 3*v2v3}) = {
    return(deriv_poly(f,g,uri));
};

/* ---- post-Lie recursion and Grossman-Larson products ---- */

post_lie_triangle(a, b, {tr_num = 2}) = {
    my(ret);
    ret = Str("tr_",tr_num,"(",a,",",b,")");
    return(ret);
};

post_lie_recursion({A = [v1,v2,v3]}, {B = [v5]}, {tr_num = 2}) = {
    my(ret = vector((#A)!), tmp, num = 1);
    if(#B != 1, error("Second input must be a list of one letter!"));
    if(A == [], return([[1, Str(B[1])]]));
    if(#A == 1, return([[1, post_lie_triangle(A[1], B[1], tr_num)]]));
    tmp = post_lie_recursion(A[^1], B, tr_num);
    for(m = 1, #tmp, 
        ret[num] = [tmp[m][1], post_lie_triangle(A[1], tmp[m][2], tr_num)];
        num++
    );
    for(n = 2, #A,        
        tmp = post_lie_recursion(concat([A[2..n-1], [post_lie_triangle(A[1], A[n], tr_num)], A[n+1..#A]]), B, tr_num);
        for(m = 1, #tmp, 
            ret[num] = [-tmp[m][1], tmp[m][2]];
            num++
        );
    );
    return(ret);
};

/* extended post-lie product on universal enveloping algebra */

post_lie_product_word({A = [v0,v2]}, {B = [v2,v0,v1]}, {tr_num = 2}) = {
    my(ret = 0, tmpA, tmp, tmp_vec, tmp_Vars, tmp_coeffs, iter_vec, tmp_bool, conc_vars, conc_coeffs);
    if(B == [], return(ret));
    if(A == [], return(eval(strjoin(B))));
    tr_num = str_to_tr_num(tr_num);
    tmpA = coprod_shuffle_word(A, #B-1);
    for(aa = 1, #tmpA,
        tmp = tmpA[aa];
        tmp_vec = vector(#B, nn, post_lie_recursion(tmp[nn], [B[nn]], tr_num));
        tmp_vec = vector(#tmp_vec, n, vector(#tmp_vec[n], nn, tmp_vec[n][nn][1] * eval(tmp_vec[n][nn][2]))); /* applying eval calls tr_0, tr_1, or tr_2 (cf. post_lie_triangle) */
        tmp_vec = eval(tmp_vec);
        tmp_vars = vector(#tmp_vec, n, vector(#tmp_vec[n], nn, variables(tmp_vec[n][nn])));
        tmp_coeffs = vector(#tmp_vars, n, vector(#tmp_vars[n], nn, vector(#tmp_vars[n][nn], nnn, polcoef(tmp_vec[n][nn], 1, tmp_vars[n][nn][nnn]))));
        iter_vec = vector(#tmp_vec, ii, #tmp_vec[ii]-1);
        iter_vec = gen_mult_vec(iter_vec);
        iter_vec = vector(#iter_vec, n, vector(#iter_vec[n], nn, iter_vec[n][nn]+1));
        iter_vec = vector(#iter_vec, i, vector(#tmp_vec, ii, concat(Str("[",ii,"]"), Str("[",iter_vec[i][ii],"]"))));
        tmp_bool = 1;
        for(n = 1, #tmp_vec, if(!tmp_vec[n], tmp_bool = 0;)); /* tests whether a factor vanishes */
        if(tmp_bool,
            for(n = 1, #iter_vec,
                conc_vars = vector(#iter_vec[n], nn, eval(concat(Str(tmp_vars),iter_vec[n][nn])));
                conc_vars = word_concat_list(conc_vars);
                conc_coeffs = vector(#iter_vec[n], nn, eval(concat(Str(tmp_coeffs),iter_vec[n][nn])));
                conc_coeffs = mult_list(conc_coeffs);
                if(conc_vars != [] && conc_coeffs !=  [],
                    ret += conc_coeffs * conc_vars~;
                );
            );
        );
    );
    return(ret);
};

post_lie_product({f = 2*v0v2v3 - 4*v1v0v2}, {g = v5 + 3*v2v3}, {tr_num = 2}) = {
    my(var_f, var_g, coeff_f, coeff_g, tmp_f, tmp_g, ret = 0);
    [coeff_f, var_f] = poly_to_indexset(f);
    [coeff_g, var_g] = poly_to_indexset(g);
    for(i = 1, #var_f,
        for(j = 1, #var_g,
            tmp_f = word_to_letter_index(var_f[i]);
            tmp_g = word_to_letter_index(var_g[j]);
            ret += coeff_f[i] * coeff_g[j] * post_lie_product_word(tmp_f, tmp_g, tr_num);
        );
    );
    return(ret);
};

/* Grossman-Larson products */

glp_word({A = [v1, v2, v3]}, {B = [v1, v2]}, {tr_num = 2}) = {
    my(ret = 0, tmpA, tmp, tmp_bool, tmp_vec, tmp_conc, tmp_coeffs, tmp_res, iter_vec);
    if(B == [], return(eval(strjoin(A))));
    tr_num = str_to_tr_num(tr_num);
    tmpA = coprod_shuffle_word(A, #B);
    for(aa=1,#tmpA,
        tmp = tmpA[aa];
        tmp_vec = vector(#B, nn, post_lie_recursion(tmp[nn+1],[B[nn]], tr_num));
        tmp_vec = vector(#tmp_vec, n, vector(#tmp_vec[n], nn, tmp_vec[n][nn][1] * eval(tmp_vec[n][nn][2]))); /* application of eval here indirectly applies the function tr (cf. post_lie_triangle) */
        tmp_vec = eval(tmp_vec); /* drop terms with vanishing coefficient */
        tmp_vars = vector(#tmp_vec, n, vector(#tmp_vec[n], nn, variables(tmp_vec[n][nn])));
        tmp_coeffs = vector(#tmp_vars, n, vector(#tmp_vars[n], nn, vector(#tmp_vars[n][nn], nnn, polcoef(tmp_vec[n][nn], 1, tmp_vars[n][nn][nnn]))));
        iter_vec = vector(#tmp_vec, ii, #tmp_vec[ii]-1);
        iter_vec = gen_mult_vec(iter_vec);
        iter_vec = vector(#iter_vec, n, vector(#iter_vec[n], nn, iter_vec[n][nn]+1));
        iter_vec = vector(#iter_vec, i, vector(#tmp_vec, ii, concat(Str("[",ii,"]"), Str("[",iter_vec[i][ii],"]"))));
        tmp_bool = 1;
        for(n = 1, #tmp_vec, if(!tmp_vec[n], tmp_bool = 0;)); /* tests whether a factor vanishes */
        if(tmp_bool,
            for(n = 1, #iter_vec,
                if(tmp[1] == [],
                    conc_vars = vector(#iter_vec[n], nn, eval(concat(Str(tmp_vars),iter_vec[n][nn]))),
                    conc_vars = concat([[eval(strjoin(tmp[1]))]],vector(#iter_vec[n], nn, eval(concat(Str(tmp_vars),iter_vec[n][nn]))));
                );
                conc_vars = word_concat_list(conc_vars);
                conc_coeffs = vector(#iter_vec[n], nn, eval(concat(Str(tmp_coeffs),iter_vec[n][nn])));
                conc_coeffs = mult_list(conc_coeffs);
                if(conc_vars != [] && conc_coeffs != [],
                    ret += conc_coeffs * conc_vars~;
                );
            );
        );
    );
    return(ret);
};

glp({f = 2*v0v2v3 - 4*v1v0v2}, {g = v5 + 3*v2v3}, {tr_num = 2}) = {
    my(var_f, var_g, coeff_f, coeff_g, tmp_f, tmp_g, ret = 0);
    [coeff_f, var_f] = poly_to_indexset(f);
    [coeff_g, var_g] = poly_to_indexset(g);
    for(i = 1, #var_f,
        for(j = 1, #var_g,
            tmp_f = word_to_letter_index(var_f[i]);
            tmp_g = word_to_letter_index(var_g[j]);
            ret += coeff_f[i] * coeff_g[j] * glp_word(tmp_f, tmp_g, tr_num);
        );
    );
    return(ret);
};

/* faster formulae for the post-Lie products */

act_antipode_ihara({A = [3,1,0,0,1]}, {a = 2}) = {
    my(ret = vector(2^#A), ii = 1, A_coprod, tmp);
    A_coprod = coprod_shuffle_word(A);
    for(n = 1, #A_coprod,
        tmp = antipode(A_coprod[n][1]);
        ret[ii] = [tmp[1], concat([tmp[2], a, A_coprod[n][2]])];
        ii++;
    );
    return(ret);
};

act_ihara_fast({A = [3,1,0,2]}, {a = 2}) = {
    my(ret);
    ret = act_antipode_ihara(A,a);
    ret = sum(n = 1, #ret, ret[n][1] * index_to_word(ret[n][2],v));
    return(ret);
};

act_ari_fast({A = [3,1,0,2]}, {a = 2}) = {
    my(ret, lk = 1, k, all_l, tmp_l, mult_ari, A_l, ret_tmp, ii = 1);
    if(a == 0, return([ [0,[]] ]));
    k = vector(#A);
    for(i = 1, #A,
        if(A[i] > 0,
            k[lk] = A[i];
            lk++
        );
    );
    k = k[1..lk-1];
    all_l = generate_all_l_indices(k);
    ret = vector(#all_l);
    for(n = 1, #all_l,
        tmp_l = all_l[n];
        mult_ari = ari_multiplicity(k,tmp_l);
        A_l = vector(#A);
        lk = 1;
        for(m = 1, #A, 
            if(A[m] > 0,
                A_l[m] = tmp_l[lk];
                lk++
            );
        );
        ret_tmp = act_antipode_ihara(A_l, a+vecsum(k)-vecsum(tmp_l));
        ret_tmp = vector(#ret_tmp, N, [mult_ari * ret_tmp[N][1], ret_tmp[N][2]]);
        ret[n] = ret_tmp;
    );
    ret = concat(ret);
    ret = sum(n = 1, #ret, ret[n][1] * index_to_word(ret[n][2],v));
    return(ret);
};

act_uri_letter({k = 3}, {a = 2}) = {
    if(k == 0 || k == 1, return([ [1, [a,k]] ]));
    my(ret = vector(2^(a+k-1)), mult_ari, comp, mult_uri, ii = 1);
    for(l = 1, k,
        mult_ari = ari_multiplicity([k],[l]);
        comp = composition(a+k-l);
        for(j = 1, #comp,
            mult_uri = uri_multiplicity(a, comp[j]);
            if(mult_uri != 0, 
                ret[ii] = [mult_uri * mult_ari, concat(comp[j],[l])];
                ii++;
            );
        );
    );
    return(ret[1..ii-1]);
};

act_uri_word({k = 2}, {vv = [1, [[2,[3,1],1],1]]}) = {
    my(tmp, ret = vector(5*10^4), ii = 1, tmp_uri, tmp_ret);
    tmp = strsplit(Str(vv[2]));
    for(i = 1, #tmp-2,
        if(tmp[i] != "[" && tmp[i] != "," && tmp[i] != " " && tmp[i] != "]",
            if(tmp[i+1] != "]",
                tmp_uri = act_uri_letter(k, eval(tmp[i]));
                for(j = 1, #tmp_uri,
                    tmp_ret = tmp;
                    tmp_ret[i] = Str(tmp_uri[j][2]);
                    ret[ii] = [vv[1] * tmp_uri[j][1], eval(strjoin(tmp_ret))];
                    ii++;
                );
            );
        );
    );
    ret = ret[1..ii-1];
    return(ret);
};

act_uri_vector({k = 3}, {vec = [[1, [2,1]], [-1/2, [1,1,1]], [1, [1,2]]]}) = {
    my(tmp, ret = vector(10^6), ii = 1);
    tmp = vector(#vec, i, act_uri_word(k, vec[i]));
    for(i = 1, #tmp,
        for(j = 1, #tmp[i],
            ret[ii] = tmp[i][j];
            ii++;
        );
    );
    ret = ret[1..ii-1];
    return(ret);
};

act_uri({k = [1,2,3]}, {a = 1}) = {
    my(ret);
    ret = act_uri_letter(k[#k], a);
    for(i = 1, #k-1,
        ret = act_uri_vector(k[#k-i], ret);
    );
    return(ret);
};

uri_bra2str_word({w = [1, [[1,2],3],2]}) = {
    my(tmp, ww = #w);
    if(type(w[ww]) == "t_VEC",
        tmp = uri_bra2str_word(w[ww]),
        tmp = eval(Str("v", w[ww]));
    );
    for(i = 1, ww-1,
        if( type(w[ww-i]) == "t_VEC",
            tmp = Ad_word(uri_bra2str_word(w[ww-i]), tmp),
            tmp = Ad_word(eval(Str("v", w[ww-i])), tmp)
        );
    );
    return(tmp);
};

act_uri_fast({A = [3,1,0,2]}, {a = 2}) = {
    my(tmp, ret, ii = 0);
    if(A == [], return(eval(Str("v", a))));
    tmp = act_uri(A, a);
    ret = vector(#tmp, i, tmp[i][1] * uri_bra2str_word(tmp[i][2]));
    return(vecsum(ret));
};

/* computing Grossman-Larson products via faster implementations */

glp_fast_index({ind1 = [2,1,3]}, {ind2 = [2,0,1]}, {product = ihara}) = {
    my(ind2_zeros, tmp1, tmp, tmp_ret, ret = 0, num = 1, act_str, bool_vec);
    if(ind1 == [], return(index_to_word(ind2,v)));
    if(ind2 == [], return(index_to_word(ind1,v)));
    product = product_name(product);
    act_str = Str("act_",product,"_fast");
    ind2_zeros = vector(#ind2);
    for(n = 1, #ind2,
        if(ind2[n] == 0,
            ind2_zeros[num] = n;
            num++
        );
    );
    ind2_zeros = ind2_zeros[1..num-1];
    tmp1 = coprod_shuffle_word(ind1,#ind2);
    for(aa = 1, #tmp1,
        tmp = tmp1[aa];
        bool_vec = vector(#ind2_zeros, n, tmp[ind2_zeros[n]+1]);
        if(bool_vec == vector(#ind2_zeros, n, []),
            if(tmp[2] == [],
                tmp_ret = eval(Str("v",ind2[1])),
                tmp_ret = eval(Str(act_str,"(",tmp[2],",", ind2[1],")"));
            );
            for(n = 2, #ind2,
                if(tmp[n+1] == [],
                    tmp_ret = conc_polys(tmp_ret, eval(Str("v",ind2[n]))),
                    tmp_ret = conc_polys(tmp_ret, eval(Str(act_str,"(",tmp[n+1],",", ind2[n],")")));
                );
            );
            if(tmp[1] != [],
                tmp_ret = conc_polys(index_to_word(tmp[1],v),tmp_ret);
            );
            ret += eval(tmp_ret);
        );
    );
    return(ret);
};

glp_fast_word({A = v2v1v3}, {B = v2v0v1}, {product = ihara}) = {
    return(glp_fast_index(word_to_index(A), word_to_index(B), product));
};

glp_fast({f = 3 * v2v1v0 - 3/2 * v1v3}, {g = v4 - 1/3 * v2v2 + 2 * v1v0v2}, {product = ihara}) = {
    my(f_coeffs, f_vars, g_coeffs, g_vars, ret = 0);
    [f_coeffs, f_vars] = poly_to_indexset(f);
    [g_coeffs, g_vars] = poly_to_indexset(g);
    for(n = 1, #f_vars,
        for(nn = 1, #g_vars,
            ret += f_coeffs[n] * g_coeffs[nn] * glp_fast_word(f_vars[n], g_vars[nn], product);
        );
    );
    return(ret);
};

/* using the explicit formula for glp_ihara */

glp_ihara_antipode_word({A = v2v1v3}, {B = v1v0v2}) = {
    my(A_ind, B_ind, B_km, tmpA, tmp, tmp_ret, ret = 0);
    A_ind = word_to_index(A);
    B_ind = word_to_index(B);
    B_km = index_to_km_index(B_ind);
    tmpA = coprod_shuffle_word(A_ind, #B_km-1);
    for(n = 1, #tmpA,
        tmp = tmpA[n];
        tmp_ret = tmp[1];
        sgn = 1;
        for(m = 1, (#B_km-1)/2,
            sgn *= (-1)^(#tmp[2*m]);
            tmp_ret = concat(tmp_ret, concat([vector(B_km[2*m-1]), vector(#tmp[2*m], M, tmp[2*m][#tmp[2*m]+1-M]), [B_km[2*m]], tmp[2*m+1]]));
        );
        tmp_ret = concat(tmp_ret, vector(B_km[#B_km]));
        ret += sgn * index_to_word(tmp_ret, v);
    );
    return(ret);
};

glp_ihara_antipode({A = v2v1v3 + 3*v1v0v3}, {B = -3*v0v0v2 + v3}) = {
    my(vars_A, vars_B, coeffs_A, coeffs_B, tmp_A, tmp_B, ret = 0);
    if(A == 1, return(B));
    if(B == 1, return(A));
    [coeffs_A, vars_A] = poly_to_indexset(A);
    [coeffs_B, vars_B] = poly_to_indexset(B);
    for(i = 1, #vars_A,
        for(j = 1, #vars_B,
            tmp_A = vars_A[i];
            tmp_B = vars_B[j];
            ret += coeffs_A[i] * coeffs_B[j] * glp_ihara_antipode_word(tmp_A, tmp_B);
        );
    );
    return(ret);
};