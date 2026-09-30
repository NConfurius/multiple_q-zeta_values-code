/* --------- Service functions --------- */

/* auxiliary functions (e.g. generating certain index sets, compositions etc.) */

weight({w = [0,0,1]}, {alphabet = V}) = {
    my(ret = 0);
    if(alphabet == X || alphabet == x, return(#w));
    if(alphabet == Y || alphabet == y, return(vecsum(w)));
    if(alphabet == V || alphabet == v || alphabet = B || alphabet = b, for(n = 1, #w, if(w[n] == 0, ret++)); return(ret + vecsum(w)));
    error("Input error! Implemented alphabets are X, Y, B and V.");
};

gen_mult_vec({v = [2,1,3]}) = {
    my(lv = #v, m, tmp, ii);
    m = prod(i = 1,lv, v[i]+1);
    tmp = vector(m, i, vector(lv));
    ii = 1;
    for(i = 1, lv, 
        for(j = 0, v[i], 
            for(ll = 1, ii, 
            tmp[ii*j+ll] = tmp[ll];
            tmp[ii*j+ll][i] = j
            );
        );
        ii = ii*(v[i]+1);
    );
    return(tmp);
};

composition({n = 5}) = {
    my(ret = [], tmp);
    if(n == 1, return([[1]]));
    if(n == 2, return([[2], [1,1]]));
    if(n == 3, return([[3], [2,1], [1,2], [1,1,1]]));
    if(n == 4, return([[4], [3,1], [2,2], [2,1,1], [1,3], [1,2,1], [1,1,2], [1,1,1,1]]));
    if(n > 4, 
       ret=[[n], [n-1,1], [n-2,2], [n-2,1,1] ];
       for(i = 3, n-1,
           tmp = composition(i); 
           for(j = 1, #tmp, 
               ret = concat(ret, [concat([n-i],tmp[j])]);
           );
        );
    );
    return(ret);
};

/* Similar to composition, but treats 0 as another 1 */
generate_words_V({n = 4}) = {
    my(ret = [], tmp);
    if(n == 1, return([[0], [1]]));
    if(n == 2, return([[2], [0,0], [0,1], [1,0], [1,1]]));
    if(n == 3, return([[3], [0,2], [1,2], [2,0], [2,1], [0,0,0], [0,0,1], [0,1,0], [0,1,1], [1,0,0], [1,0,1], [1,1,0], [1,1,1]]));
    if(n == 4, return([[4], [0,3], [1,3], [2,2], [3,0], [3,1], [0,0,2], [0,1,2], [0,2,0], [0,2,1], [1,0,2], [1,1,2], [1,2,0], [1,2,1], [2,0,0], [2,0,1], [2,1,0], [2,1,1], [0,0,0,0], [0,0,0,1], [0,0,1,0], [0,0,1,1], [0,1,0,0], [0,1,0,1], [0,1,1,0], [0,1,1,1], [1,0,0,0], [1,0,0,1], [1,0,1,0], [1,0,1,1], [1,1,0,0], [1,1,0,1], [1,1,1,0], [1,1,1,1]]));
    if(n > 4, 
        ret=[[n], [n-1,1], [n-1,0]];
        for(i = 2, n-1,
            tmp = generate_words_V(i); 
            for(j = 1, #tmp,
                ret = concat(ret, [concat([n-i], tmp[j])]);
            );
            if(i == n-1, 
                for(j = 1, #tmp, 
                   ret = concat(ret, [concat([0],tmp[j])]);
                );
            );
        );
    );
    return(ret);
};

commutator_bracket({x = 2 * v2v1 - v3}, {y = 3*v0 + v1v2}) = {
    my(coeff_x, coeff_y, var_x, var_y, mult, ret = 0);
    var_x = variables(x);
    var_y = variables(y);
    coeff_x = vector(#var_x, n, polcoeff(x, 1, var_x[n]));
    coeff_y = vector(#var_y, n, polcoeff(y, 1, var_y[n]));
    for(i = 1, #var_x,
        for(j = 1, #var_y,
            mult = coeff_x[i] * coeff_y[j];
            ret += mult * eval(Str(var_x[i],var_y[j]));
            ret -= mult * eval(Str(var_y[j],var_x[i]));
        );
    );
    return(ret);
};

/* concatenation product */

conc_mult({f = [[-2,1],[[[2,1],[1,3]],[[1,2]]]]}, {g = [[1,2],[[[2,0]],[[1,2],[3,0]]]]}) = {
    my(ret = [[],[]]);
    if(#f[1] != #f[2] || #g[1] != #g[2], error("Wrong input! There must be as many coefficients as words, respectively."));
    for(i = 1, #f[1],
        for(j = 1, #g[1],
            ret[1] = concat([ret[1], f[1][i]*g[1][j]]);
            ret[2] = concat([ret[2], [concat([f[2][i],g[2][j]])]]);
        );
    );
    return(ret);
};

conc({lst = [[[-2,1],[[[2,1],[1,3]],[[1,2]]]], [[1,2],[[[2,0]],[[1,2],[3,0]]]], [[1,45],[[[1,3],[2,0]],[[1,1]]]]]}) = {
    my(ret = [[],[]]);
    if(#lst == 1, return(lst[1]));
    ret = conc_mult(lst[1],lst[2]);
    for(i = 3, #lst,
        ret = conc_mult(ret,lst[i]);
    );
    return(ret);
};

conc_polys({x = 2 * v2v1 - v3}, {y = 3*v0 + v1v2}) = {
    my(coeff_x, coeff_y, var_x, var_y, ret = 0);
    if(x == 1, return(y));
    if(y == 1, return(x));
    var_x = variables(x);
    var_y = variables(y);
    coeff_x = vector(#var_x, n, polcoeff(x, 1, var_x[n]));
    coeff_y = vector(#var_y, n, polcoeff(y, 1, var_y[n]));
    for(i = 1, #var_x,
        for(j = 1, #var_y,
            ret += coeff_x[i] * coeff_y[j] * eval(Str(var_x[i],var_y[j]));
        );
    );
    return(ret);
};

word_concat({w1 = v1v2}, {w2 = v4v3}) = {
    return(eval(concat(Str(w1),Str(w2))));
};

word_concat_list({lst = [[v4v2, v1v2, v2, v3v6], [v2v1, v4v6], [v4, v2v1]]}) = {
    my(ret, num = 1);
    if(#lst == 1, return(lst[1]));
    if(#lst == 2,
        ret = vector(#lst[1] * #lst[2]);
        for(n = 1, #lst[1],
            for(m = 1, #lst[2],
                ret[num] = word_concat(lst[1][n], lst[2][m]);
                num++
            );
        );
        return(ret);
    );
    return(word_concat_list(concat([word_concat_list(lst[1..2])], lst[3..#lst])));
};

mult_list({lst = [[-2, 5, 1, 0], [2,1], [8,-10]]}) = {
    my(ret, num = 1);
    if(#lst == 1, return(lst[1]));
    if(#lst == 2, 
        ret = vector(#lst[1] * #lst[2]);
        for(n = 1, #lst[1],
            for(m = 1, #lst[2],
                ret[num] = lst[1][n] * lst[2][m];
                num++
            );
        );
        return(ret);
    );
    return(mult_list(concat([mult_list(lst[1..2])], lst[3..#lst])));
};

generate_all_l_indices({k = [2,1,3]}) = {
    my(lk = #k, m, all_l, ii);
    m = prod(i = 1, lk, k[i]);
    all_l = vector(m, i, vector(lk));
    ii = 1;
    for(i = 1, lk,
        for(j = 1, k[i],
            for(ll = 1, ii,
                all_l[ii*(j-1)+ll] = all_l[ll];
                all_l[ii*(j-1)+ll][i] = j
            );
        );
        ii = ii*(k[i]);
    );
    return(all_l);
};

Ad_letter_word({v = [1]}, {w = [[1,[0,1]],[7,[2,3]]]})={
    my(var = #w, ret);
    ret = vector(2*var, i, if(i <= var, [w[i][1], vector(#w[i][2]+1, j, if(j==1, v[1], w[i][2][j-1]))],
    [-w[i-var][1], vector(#w[i-var][2]+1, j, if(j == #w[i-var][2]+1, v[1], w[i-var][2][j]))]));
    return(ret);
};

Ad_vec_word({a = [1,2,3]}, {w = [[1,[0,1,7]]]})={
    if(a == [], 
        return(w),
        return(Ad_vec_word(a[1..#a-1], Ad_letter_word([a[#a]], w)));
    );
};

tensor_readable({tensor = [[v2], [v2,v3]]}) = {
    if(tensor[1] == [], 
        return(eval(Str("one_",strjoin(tensor[2]))));
    );
    if(tensor[2] == [],
        return(eval(Str(strjoin(tensor[1]), "_one")));
    );
    return(eval(Str(strjoin(tensor[1]), "_", strjoin(tensor[2]))));
};

tensor_readable_V({tensor = [[2], [2,3]]}) = {
    tensor = vector(#tensor, n, index_to_word(tensor[n], v));
    if(tensor[1] == 1, 
        tensor[1] = one;
    );
    if(tensor[2] == 1,
        tensor[2] = one;
    );
    return(eval(strjoin(tensor,"_")));
};

coprod_readable({coprod = [[[v1, v2], []], [[v1], [v2]], [[v2], [v1]], [[], [v1, v2]]]}) = {
    return(apply(tensor_readable, coprod));
};

Ad_word({v=v1}, {w = v0v1+v2v3})={
    my(ret=0, var_w, var_v);
    var_w=variables(w);
    var_v=variables(v); 
    for(i=1, #var_w, 
        for(j=1, #var_v,
            ret = ret + polcoeff(w,1,var_w[i]) * polcoeff(v,1,var_v[j]) * (eval(Str(var_v[j],var_w[i])) - eval(Str(var_w[i],var_v[j]))); 
    ));  
    return(ret);
};

/* k-level from Burmester--Kuehn (2025), Conj. 4.29 */

k_level({w = [2,0,0,1,2,4]}, {k = 2}) = {
    my(num_k = 0, l = #w);
    for(n = 1, l, 
        if(w[n] == k, num_k++)
    );
    return(l-num_k);
};

/* --------- conversion functions --------- */

tr_num_to_str({tr_num = 2}) = {
    if( tr_num == 0, return("ihara"),
        tr_num == 1, return("ari"),
        tr_num == 2, return("uri"),
        error("Input is not associated to an implemented post-Lie product (0: ihara, 1: ari, 2: uri).");
    );
};

product_name({product = uri}) = {
    if((type(product) == "t_INT" && product > 2) || (type(product) != "t_INT" && Str(product) != "ihara" && Str(product) != "ari" && Str(product) != "uri"),
        error("Specified product is not implemented. Choose either ihara, ari or uri as input.");
    );
    if(type(product) == "t_INT", product = tr_num_to_str(product), product = Str(product));    
    return(product);
};

str_to_tr_num({tr_num = "ari"}) = {
    my(tmp_tr);
    if(type(tr_num) == "t_INT" && tr_num <= 2, 
        return(tr_num),
        tmp_tr = product_name(tr_num);
        if( tmp_tr == "ihara", return(0),
            tmp_tr == "ari", return(1),
            tmp_tr == "uri", return(2)
        );
    );
    error("Specified product is not implemented. Choose either ihara, ari or uri as input.");
};

v_to_b_letter({k = 3}) = {
    my(ret = [[],[]], tmp);
    if(k < 2, return([[1],[[k]]]));
    tmp = composition(k);
    ret[1] = vector(#tmp, i, (-1)^(#tmp[i]+1)/(#tmp[i]));
    ret[2] = tmp;
    return(ret);
};

v_to_b_word({w = v0v2v1}) = {
    my(ret = 0, tmp, w_split);
    w_split = strsplit(Str(w),"v")[^1];
    tmp = conc(vector(#w_split, i, v_to_b_letter(eval(w_split[i]))));
    for(n = 1, #tmp[1],
        ret += tmp[1][n] * eval(Str("b",strjoin(tmp[2][n],"b")));
    );
    return(ret);
};

v_to_b({f = v0v2v1 + 3*v3v2}) = {
    my(ret = 0, f_vars, f_coeffs);
    [f_coeffs, f_vars] = poly_to_indexset(f);
    for(n = 1, #f_vars,
        ret += f_coeffs[n] * v_to_b_word(f_vars[n]);
    );
    return(ret);
};

b_to_v_letter({k = 3}) = {
    my(ret = [[],[]], tmp);
    if(k < 2, return([[1],[[k]]]));
    tmp = composition(k);
    ret[1] = vector(#tmp, i, 1/(#tmp[i])!);
    ret[2] = tmp;
    return(ret);
};

b_to_v_word({w = b0b3b1}) = {
    my(ret = 0, tmp, w_split);
    w_split = strsplit(Str(w),"b")[^1];
    tmp = conc(vector(#w_split, i, b_to_v_letter(eval(w_split[i]))));
    for(n = 1, #tmp[1],
        ret += tmp[1][n] * eval(Str("v",strjoin(tmp[2][n],"v")));
    );
    return(ret);
};

b_to_v({f = b0b2b1 + 3*b3b2}) = {
    my(ret = 0, f_vars, f_coeffs);
    [f_coeffs, f_vars] = poly_to_indexset(f);
    for(n = 1, #f_vars,
        ret += f_coeffs[n] * b_to_v_word(f_vars[n]);
    );
    return(ret);
};

word_to_letter_index({w = v1v12v0}) = {
    my(letter);
    if(w == one || w == 1, return([]));
    letter = strsplit(Str(w))[1];
    w = strsplit(Str(w),letter)[^1];
    w = vector(#w, n, Str(letter,w[n]));
    return(eval(w));
};

word_to_index({w = v1v12v0}) = {
    if(w == one || w == 1, return([]));
    my(letter);
    letter = strsplit(Str(w))[1];
    w = strsplit(Str(w),letter)[^1];
    return(eval(w));
};

index_to_letter_index({ind = [1,12,0]}, {letter = v}) = {
    letter = Str(letter);
    ind = vector(#ind, n, eval(Str(letter,ind[n])));
    return(ind);
};

index_to_word({ind = [1,12,0]}, {letter = v}) = {
    if(ind == [], return(1));
    return(eval(strjoin(index_to_letter_index(ind, letter))));
};

poly_to_indexset({f = 3 * v3v1 - 5 * v1v0v2}) = {
    my(vars, coeffs);
    vars = variables(eval(f));
    coeffs = vector(#vars, n, polcoef(f, 1, vars[n]));
    return([coeffs, vars]);
};

/* index_to_km_index
returns vector of the form [m0,k1,m1,...,kd,md] w/ mi>=0, ki>= 1
where mi is the number of zeroes between ki and its successor
*/

index_to_km_index({vec = [0,1,2,0,0,3,0]}) = {
    my(num = 0, ret = [], d = 0);
    if(vec == [], return(vec));
    for(n = 1, #vec,
        if(vec[n] == 0,
            num++,
            ret = concat(ret,[num,vec[n]]);
            num = 0
        );
    );
    return(concat(ret,[num]));
};

/* index_to_zero_subindices
rewrites given index as consecutive non-zero- and zero-subwords, resp.
useful to improve running time of exp_hoffman / log_hoffman
e.g. input [0, 0, 2, 1, 0, 3, 2, 0] returns [[0,0], [2,1], [0], [3,2], [0]]
*/

index_to_zero_subindices({ind = [0,0,2,1,0,3,2,0]}) = {
    my(num = 1, ind_bool, vec_tmp = []);
    ind_bool = vector(#ind, n, if(ind[n] > 0, 1));
    for(n = 1, #ind-1,
        if((ind_bool[n] + ind_bool[n+1])%2 == 1,
            vec_tmp = concat(vec_tmp, [ind[num..n]]);
            num = n+1;
        );
    );
    return(concat(vec_tmp, [ind[num..#ind]]));
};

/* hoffman isomorphisms between quasi-shuffle algebras over B and V */

exp_hoffman_word({w = v2v1v0v0v3v2v0}, {target_alphabet = b}) = {
    my(alphabet, comps, ret, tmp_coeffs, tmp_vars, w_ind, w_subwords);
    alphabet = strsplit(Str(w))[1];
    w_ind = word_to_index(w);
    w_subwords = index_to_zero_subindices(w_ind);
    comps = vector(#w_subwords);
    ret = vector(#w_subwords);
    for(n = 1, #w_subwords, 
        if(w_subwords[n], /* skip zero indices */
            comps[n] = composition(#w_subwords[n]);
        );
    );
    for(n = 1, #comps,
        comp = comps[n];
        if(comp == 0,
            ret[n] = [[1], [w_subwords[n]]],
            tmp_coeffs = vector(#comp, m, 1/prod(i=1, #comp[m], comp[m][i]!));
            tmp_vars = vector(#comp, m, 
                vector(#comp[m], M, 
                    sum(i = 1+sum(j=1, M-1, comp[m][j]), sum(j=1, M, comp[m][j]), 
                        w_subwords[n][i]
                    );
                );
            );
            ret[n] = [tmp_coeffs, tmp_vars];
        );
    );
    ret = conc(ret);
    ret[2] = vector(#ret[2], m, index_to_word(ret[2][m], target_alphabet));
    return(ret[1] * ret[2]~);
};

exp_hoffman({f = v2v1v0v0v3v2v0 + 1/2 * v5v3v0v2}, {target_alphabet = b}) = {
    my(f_coeffs, f_vars, ret = 0);
    [f_coeffs, f_vars] = poly_to_indexset(f);
    for(n = 1, #f_vars,
        ret += f_coeffs[n] * exp_hoffman_word(f_vars[n], target_alphabet);
    );
    return(ret);
};

log_hoffman_word({w = b2b1b0b0b3b2b0}, {target_alphabet = v}) = {
    my(alphabet, comps, ret, tmp_coeffs, tmp_vars, w_ind, w_subwords);
    alphabet = strsplit(Str(w))[1];
    w_ind = word_to_index(w);
    w_subwords = index_to_zero_subindices(w_ind);
    comps = vector(#w_subwords);
    ret = vector(#w_subwords);
    for(n = 1, #w_subwords, 
        if(w_subwords[n],
            comps[n] = composition(#w_subwords[n]);
        );
    );
    for(n = 1, #comps,
        comp = comps[n];
        if(comp == 0,
            ret[n] = [[1], [w_subwords[n]]],
            tmp_coeffs = vector(#comp, m, (-1)^(#w_subwords[n]-#comp[m])/(vecprod(comp[m])));
            tmp_vars = vector(#comp, m, 
                vector(#comp[m], M, 
                    sum(i = 1+sum(j=1,M-1,comp[m][j]), sum(j=1,M,comp[m][j]), 
                        w_subwords[n][i])
                );
            );
            ret[n] = [tmp_coeffs, tmp_vars];
        );
    );
    ret = conc(ret);
    ret[2] = vector(#ret[2], m, index_to_word(ret[2][m], target_alphabet));
    return(ret[1] * ret[2]~);
};

log_hoffman({f = v2v1v0v0v3v2v0 + 1/2 * v5v3v0v2}, {target_alphabet = v}) = {
    my(f_coeffs, f_vars, ret = 0);
    [f_coeffs, f_vars] = poly_to_indexset(f);
    for(n = 1, #f_vars,
        ret += f_coeffs[n] * log_hoffman_word(f_vars[n], target_alphabet);
    );
    return(ret);
};

/* ---- involutions ---- */

tau_B_word({w = b3b0b0b2b1b0}) = {
    my(ind, ind_km, len, d, ret, pos);
    ind = word_to_index(w);
    ind_km = index_to_km_index(ind);
    if(ind_km[1] != 0, return(w));
    len = #ind_km;
    d = (len-1)/2;
    ret = vector(sum(n = 1, d, ind_km[2*n]));
    pos = 1;
    for(n = 0, d-1,
        ret[pos] = ind_km[len-2*n]+1;
        pos += ind_km[len-1-2*n];
    );
    return(index_to_word(ret,b));
};

tau_B({f = b3b0b1b0b0 + 2*b2b0b1}) = {
    my(f_vars, f_coeffs, ret = 0);
    [f_coeffs, f_vars] = poly_to_indexset(f);
    for(n = 1, #f_vars, 
        ret += f_coeffs[n] * tau_B_word(f_vars[n]);
    );
    return(ret);
};

tau_V_word({w = v3v2v0v1v2}) = {
    my(ret, ret_vars, ret_coeffs);
    if(w == one, return(one));
    ret = exp_hoffman(w, b);
    [ret_coeffs, ret_vars] = poly_to_indexset(ret);
    ret_vars = apply(tau_B_word, ret_vars);
    ret = ret_coeffs * ret_vars~;
    return(log_hoffman(ret, v));
};

tau_V({f = v3v2v0v1v2 + 2*v2v0v1}) = {
    my(f_vars, f_coeffs, ret = 0);
    [f_coeffs, f_vars] = poly_to_indexset(f);
    for(n = 1, #f_vars, 
        ret += f_coeffs[n] * tau_V_word(f_vars[n]);
    );
    return(ret);
};

/*
tau_V_tensor
applies tau_V to tensors (on both tensor-factors).
the underline (_) stands for the tensor product, e.g. one_v1v2 is (empty word) \otimes v_1v_2.
*/

tau_V_tensor({A = one_v1v2 + 2*v2_v1 + v1v2_one}) = {
    my(A_vars, A_coeffs, tmp, ret = 0, ret_tmp, tensor_tmp, vars_l, vars_r, coeffs_l, coeffs_r);
    [A_coeffs, A_vars] = poly_to_indexset(A);
    tmp = eval(vector(#A_vars, n, strsplit(Str(A_vars[n]),"_")));
    tmp = vector(#tmp, n, apply(tau_V,tmp[n]));
    for(n = 1, #tmp,
        ret_tmp = 0;
        tensor_tmp = tmp[n];
        [coeffs_l, vars_l] = poly_to_indexset(tensor_tmp[1]);
        [coeffs_r, vars_r] = poly_to_indexset(tensor_tmp[2]);
        for(m = 1, #vars_l,
            for(mm = 1, #vars_r,
                ret_tmp += coeffs_l[m] * coeffs_r[mm] * eval(Str(vars_l[m],"_",vars_r[mm]));
            );
        );
    ret += A_coeffs[n] * ret_tmp;
    );
    return(ret);
};

tau_V_dual_aux({w = v3v0v0}) = {
    my(k, comp_k, m, comp_m, l, t, ind, tmp_ind, tmp_pos, ret = 0);
    ind = word_to_index(w);
    if(ind[2..#ind] != vector(#ind-1), error("Input must be of the form vkv0..v0 for some positive index k."));
    k = ind[1];
    m = #ind-1;
    comp_k = composition(k);
    comp_m = composition(m+1);
    for(n = 1, #comp_k,
        l = comp_k[n];
        tmp_ind = vector(k-1);
        tmp_pos = l[#l];
        for(m = 1, #l-1,
            tmp_ind[tmp_pos] = 1;
            tmp_pos += l[#l-m];
        );
        for(nn = 1, #comp_m,
            t = comp_m[nn];
            ret += (-1)^(#l+1)/((#t)! * #l) * index_to_word(concat(t,tmp_ind),v);
        );
    );
    [ret_coefs, ret_vars] = poly_to_indexset(ret);
    return([ret_coefs, apply(word_to_index, ret_vars)]);
};

tau_V_dual_word({w = v3v0v0v2v0v1v1v0}) = {
    my(w_ind, lst_ind, pos, tmp_ret);
    if(w == one, return(one));
    w_ind = word_to_index(w);
    if(w_ind[1] == 0, return(w));
    lst_ind = [];
    pos = 2;
    while(pos <= #w_ind, 
        if(w_ind[pos] == 0, 
            pos++,
            lst_ind = concat(lst_ind, [w_ind[1..pos-1]]); 
            w_ind = w_ind[pos..#w_ind]; 
            pos = 2;
        );
    );
    lst_ind = concat(lst_ind, [w_ind]);
    lst_ind = vector(#lst_ind, n, index_to_word(lst_ind[n],v));
    tmp_ret = apply(tau_V_dual_aux, lst_ind);
    tmp_ret = vector(#tmp_ret, n, tmp_ret[#tmp_ret+1-n]);
    tmp_ret = conc(tmp_ret);
    tmp_ret[2] = vector(#tmp_ret[2], n, index_to_word(tmp_ret[2][n],v));
    return(tmp_ret[1] * tmp_ret[2]~);
};

tau_V_dual({f = v3v0v1v0v0 + 2*v2v0v1}) = {
    my(f_vars, f_coeffs, ret = 0);
    [f_coeffs, f_vars] = poly_to_indexset(f);
    for(n = 1, #f_vars, 
        ret += f_coeffs[n] * tau_V_dual_word(f_vars[n]);
    );
    return(ret);
};