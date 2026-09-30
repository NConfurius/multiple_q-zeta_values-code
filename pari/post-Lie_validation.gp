/* ---------- test post-Lie structures ------------ */

/* test defining compatibitily of post-Lie product \tr and Lie bracket [-,-], i.e. for Lie elements x,y,z:
x\tr [y,z] = [x\tr y, z] + [y, x\tr z] and 
[x,y] \tr z = xy\tr z - yx\tr z */
test_post_lie({x = v3v0 - v0v3}, {y = v2}, {z = v3}, {product = uri}) = {
    my(res1, res2, bool1, bool2);
    product = eval(product_name(product));
    res1 = deriv_poly(x, commutator_bracket(y,z), product);
    res2 = commutator_bracket(deriv_poly(x, y, product), z) + commutator_bracket(y, deriv_poly(x, z, product));
    bool1 = res1 == res2;

    res1 = deriv_poly(commutator_bracket(x,y), z, product);
    res2 = deriv_poly(x, deriv_poly(y, z, product), product) - deriv_poly(deriv_poly(x, y, product), z, product) - deriv_poly(y,deriv_poly(x, z, product), product) + deriv_poly(deriv_poly(y, x, product), z, product);
    bool2 = res1 == res2;
    if(bool1 && bool2, 
        return("True"), 
        return("False")
    );
};

/* test post-Lie bracket:  \glp(x,y) - \glp(y,x) = x\tr y - y\tr x + [x,y], for Lie elements x and y. */
test_glp({x = v3v0 - v0v3}, {y = v2}, {tr_num = 2}) = {
    my(res1 = 0, res2 = 0);
    res1 = glp(x, y, tr_num) - glp(y, x, tr_num);
    res2 = post_lie_product(x, y, tr_num) - post_lie_product(y, x, tr_num) + commutator_bracket(x,y);
    if(res1 == res2, 
        return("True"), 
        return("False")
    );
};

/* following two functions: test if coproduct is an algebra morphism and vice versa, i.e. \Delta(w1 * w2) = \Delta(w1) * \Delta(w2). */

/* testing Grossman-Larson product(s) and shuffle coproduct */
test_morphism({w1 = v2v3}, {w2 = v1v0v4}, {tr_num = 2}) = {
    my(res_l, res_r, res1 = 0, res2 = 0, w1_ind, w2_ind, coprod_w1, coprod_w2, tmp1, tmp2, vars_l, vars_r, coeffs_l, coeffs_r, vars_ret, coeffs_ret, num, glp_prod, vars_prod, coeffs_prod);
    w1_ind = word_to_letter_index(w1);
    w2_ind = word_to_letter_index(w2);
    coprod_w1 = coprod_shuffle_word(w1_ind);
    coprod_w2 = coprod_shuffle_word(w2_ind);
    for(n = 1, #coprod_w1,
        tmp1 = coprod_w1[n];
        for(nn = 1, #coprod_w2,
            tmp2 = coprod_w2[nn];
            if(tmp1[1] != [] && tmp2[1] != [],
                res_l = glp(eval(strjoin(tmp1[1])), eval(strjoin(tmp2[1])), tr_num),
                tmp1[1] == [] && tmp2[1] == [],
                res_l = one,
                res_l = eval(strjoin(concat(tmp1[1], tmp2[1])));
            );
            if(tmp1[2] != [] && tmp2[2] != [],
                res_r = glp(eval(strjoin(tmp1[2])), eval(strjoin(tmp2[2])), tr_num),
                tmp1[2] == [] && tmp2[2] == [],
                res_r = one,
                res_r = eval(strjoin(concat(tmp1[2], tmp2[2])));
            );
            [coeffs_l, vars_l] = poly_to_indexset(res_l);
            [coeffs_r, vars_r] = poly_to_indexset(res_r);
            vars_l = apply(word_to_letter_index, vars_l);
            vars_r = apply(word_to_letter_index, vars_r);
            vars_ret = vector(#vars_l * #vars_r);
            coeffs_ret = vars_ret;
            num = 1;
            for(i = 1, #vars_l,
                for(ii = 1, #vars_r,
                    vars_ret[num] = [vars_l[i], vars_r[ii]];
                    coeffs_ret[num] = coeffs_l[i] * coeffs_r[ii];
                    num++;
                );
            );
            vars_ret = coprod_readable(vars_ret);
            res1 += coeffs_ret * vars_ret~;
        );
    );
    glp_prod = glp(w1, w2, tr_num);
    [coeffs_prod, vars_prod] = poly_to_indexset(glp_prod);
    res2 = apply(coprod_shuffle_word, apply(word_to_letter_index, vars_prod));
    res2 = apply(coprod_readable, res2);
    res2 = sum(n = 1, #res2, vecsum(coeffs_prod[n] * res2[n]));
    if(res1 == res2,
        return("True"),
        return("False");
    );
};

/* testing shuffle product and coproduct dual to Grossman-Larson product(s) */
test_duality({w1 = v2v1}, {w2 = v0v2}, {tr_num = 2}) = {
    my(res1 = 0, res2 = 0, w1_ind, w2_ind, sh_prod, sh_prod_l, sh_prod_r, tmp_coprod, coprod1, coprod2, tmp1, tmp2, num, vars_tmp);
    w1_ind = word_to_index(w1);
    w2_ind = word_to_index(w2);
    sh_prod = shuffle_prod(w1_ind, w2_ind);
    for(n = 1, #sh_prod,
        res1 += coprod_dual_glp_word(sh_prod[n], tr_num);
    );
    coprod1 = poly_to_indexset(coprod_dual_glp_word(w1_ind, tr_num));
    coprod1[2] = eval(apply(tensor -> strsplit(Str(tensor),"_"), coprod1[2]));
    coprod1[2] = vector(#coprod1[2], n, apply(word_to_letter_index, coprod1[2][n]));
    coprod2 = poly_to_indexset(coprod_dual_glp_word(w2_ind, tr_num));
    coprod2[2] = eval(apply(tensor -> strsplit(Str(tensor),"_"), coprod2[2]));
    coprod2[2] = vector(#coprod2[2], n, apply(word_to_letter_index, coprod2[2][n]));
    for(n = 1, #coprod1[2],
        tmp1 = coprod1[2][n];
        for(nn = 1, #coprod2[2],
            tmp2 = coprod2[2][nn];
            sh_prod_l = shuffle_prod(tmp1[1], tmp2[1]);
            sh_prod_r = shuffle_prod(tmp1[2], tmp2[2]);
            num = 1;
            vars_tmp = vector(#sh_prod_l * #sh_prod_r);
            for(i = 1, #sh_prod_l,
                for(ii = 1, #sh_prod_r,
                    vars_tmp[num] = [sh_prod_l[i], sh_prod_r[ii]];
                    num++
                );
            );
            res2 += vecsum(coprod1[1][n] * coprod2[1][nn] * coprod_readable(vars_tmp));
        );
    );
    if(res1 == res2,
        return("True"),
        return("False");
    );
};

test_act_ihara_fast({A = v3v1v0v0v2}, {va = v2}) = {
    my(res1, res2, a = word_to_index(va));
    if(#a != 1 || a == [0] && va != v0, error("Second input must be a single letter, e.g. v2"));
    res1 = post_lie_product(A, va, 0);
    res2 = act_ihara_fast(word_to_index(A), a[1]);
    if(res1 == res2,
        return("True"),
        return("False");
    );
};

test_act_ari_fast({A = v3v1v0v0v2}, {va = v2}) = {
    my(res1, res2, a = word_to_index(va));
    if(#a != 1 || a == [0] && va != v0, error("Second input must be a single letter, e.g. v2"));
    res1 = post_lie_product(A, va, 1);
    res2 = act_ari_fast(word_to_index(A), a[1]);
    if(res1 == res2,
        return("True"),
        return("False");
    );
};

test_act_uri_fast({A = v3v1v0v0v2}, {va = v2}) = {
    my(res1, res2, a = word_to_index(va),time);
    if(#a != 1 || a == [0] && va != v0, error("Second input must be a single letter, e.g. v2"));
    res1 = post_lie_product(A, va, 2);
    res2 = act_uri_fast(word_to_index(A), a[1]);
    if(res1 == res2,
        return("True"),
        return("False");
    );
};

test_glp_fast({A = v3v1v0v0v2}, {B = v1v0v4}, {product = uri}) = {
    my(res1, res2);
    res1 = glp(A, B, product);
    res2 = glp_fast(A, B, product);
    if(res1 == res2,
        return("True"),
        return("False")
    );
};