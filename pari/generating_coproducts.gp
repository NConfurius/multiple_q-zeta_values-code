/*
local_path is the directory (starting at the current working directory) that is used to save the generated binary files
Note the final "/" at the end of the path.
*/

local_path = ("qmzv_dual_coproduct/");

data_exists(data, {path = local_path}) = {
    my(tmp);
    tmp = strsplit(Str(path), "/");
    if(tmp[#tmp] != "", path = Str(path,"/"));
    if(data == "",
        return(!extern(Str("test -d ", path, data, " ; echo $?")));
    );
    return(!extern(Str("test -f ", path, data, " ; echo $?")));
};

/*
computing all products upto to weight wt.
writing the results as binaries to local_path at the start of this file by default
input opt = 1 deletes old data before generating new files
*/

generate_binaries_words({k = 6}, {opt = 0}, {path = local_path}) = {
    my(lst_tmp = [], lst_pairs_tmp, lst_words, tmp, tmp_prod, filename, ii=1);
    filename = Str("lst_words_",k);
    if(!data_exists("",path),
        extern(Str("mkdir ",path));
    );
    if(opt, 
        if(data_exists(filename, path),
            extern(Str("rm ",path, filename));
            print(Str(path,filename," has been deleted."));
        );
    );
    if(!data_exists(filename, path),
        lst_tmp = Set(generate_words_V(k));
        lst_pairs_tmp = vector(2^6 * #lst_tmp);
        for(n = 1, #lst_tmp,
            lst_pairs_tmp[ii] = [[], lst_tmp[n]];
            ii++
        );
        for(i = 1, #lst_tmp,
            if(#lst_tmp[i] > 1,
                tmp = lst_tmp[i];
                for(n = 1, #tmp-1,
                    lst_pairs_tmp[ii] = [tmp[1..n],tmp[n+1..#tmp]];
                    ii++
                );
            );
        );
        for(n = 1, #lst_tmp,
            lst_pairs_tmp[ii] = [lst_tmp[n], []];
            ii++
        );
        lst_pairs_tmp = lst_pairs_tmp[1..ii-1];
        lst_words = concat([lst_tmp], [lst_pairs_tmp]);
        writebin(Str(path,filename), lst_words);
        print(Str(path,filename," has been created."));
    );
};

generate_binaries_glp_products({k = 6}, {product = uri}, {opt = 0}, {path = local_path}) = {
    my(filename, glp_prod_str, lst_words, lst_words_pairs, mat, tmp, tmp_var, tmp_coeff, tmp_vec);
    product = product_name(product);
    filename = Str("lst_",product,"_glp_",k);
    if(opt && data_exists(filename, path),
        extern(Str("rm ", path, filename));
        print(Str(path, filename," has been deleted."));
    );
    if(!data_exists(filename, path),
        glp_prod_str = Str("glp_",product,"_fast");
        if(!data_exists(Str("lst_words_",k), path),
            generate_binaries_words(k, 1, path);
        );
        [lst_words, lst_words_pairs] = read(Str(path, "lst_words_",k));
        ttime = getwalltime();
        ctime = getabstime();
        mat = matrix(#lst_words, #lst_words_pairs);
        lst_words_v = apply(w->index_to_word(w,v), lst_words);
        lst_words_pairs_v = apply(p->[index_to_word(p[1],v),index_to_word(p[2],v)], lst_words_pairs);
        exportall(); /* needed for parallel computation via parfor */
        parfor(n = 1, #lst_words_pairs,
            glp_fast_index(lst_words_pairs[n][1], lst_words_pairs[n][2], product),
            tmp_res,
            mat[,n] = vector(#lst_words, n, polcoef(tmp_res,1,lst_words_v[n]))~;
        );
        print("finished computing all ", #mat, " Grossman-Larson products in weight ",k);
        print("CPU time: ", floor(getabstime()-ctime), "ms. Real time: ", floor(getwalltime()-ttime),"ms.");
        writebin(Str(path, filename),mat);
        print(Str(path, filename, " has been created."));
    );
};


/* coproducts dual to Grossman-Larson products
note: coprod_dual_glp_word needs binaries generated via the functions "generate_binaries_words" "generate_binaries_glp_products" from "generating_coproducts.gp" in subfolder local_path
If files do not exist, they are computed in the process.
*/

coprod_dual_glp_word({w = [0,2,1,0]}, {product = uri}, {path = local_path}) = {
    my(filename, k, mat, coeffs, ii = 1, ind_w, lst_ind, lst_words, lst_words_pairs, pairs);
    if( w == [],  return(one_one),
        w == [0], return(one_v0 + v0_one),
        w == [1], return(one_v1 + v1_one);
    );
    product = product_name(product);
    k = weight(w, V);
    filename = Str("lst_",product,"_glp_",k);
    if(!data_exists(filename, path),
        generate_binaries_glp_products(k, product, 0, path);
    );
    mat = read(Str(path, filename));
    [lst_words, lst_words_pairs] = read(Str(path, "lst_words_",k));
    ind_w = setsearch(lst_words, w);
    coeffs = mat[ind_w,];
    lst_ind = vector(#coeffs);
    for(n = 1, #coeffs,
        if(coeffs[n] != 0,
            lst_ind[ii] = n;
            ii++
        );
    );
    lst_ind = lst_ind[1..ii-1];
    coeffs = vector(#lst_ind, n, coeffs[lst_ind[n]]);
    pairs = vector(#lst_ind, n, lst_words_pairs[lst_ind[n]]);
    return(coeffs * apply(tensor_readable_V, pairs)~);
};

coprod_dual_glp({f = 3 * v1v2 - v3v2}, {product = uri}, {path = local_path}) = {
    my(f_vars, f_coeffs, ret = 0);
    [f_coeffs, f_vars] = poly_to_indexset(f);
    f_vars = apply(word_to_index,f_vars);
    for(n = 1, #f_vars,
        ret += f_coeffs[n] * coprod_dual_glp_word(f_vars[n], product, path);
    );
    return(ret);
};

/* ---------- test k-level conjecture: ------------ */

klevel_conjecture_test({k = 1}, {wt = 5}, {product = ari}, {path = local_path}) = {
    my(filename_product = Str("lst_",product,"_glp_", wt), filename_words = Str("lst_words_", wt), words, pairs, mat, word, word_level, counter, coeffs);
    if(data_exists(filename_product, path),
        mat = read(Str(path, filename_product)),
        print("No file named ",filename_product," exist at ", path,". Call generate_binaries_glp_products(",wt,",",product,",",0,",",path,") and try again.");
        error();
    );
    if(data_exists(filename_words, path),
        [words,pairs] = read(Str(path, filename_words)),
        print("No file named ",filename_words," exist at ", path,". Call generate_binaries_words(",wt,",",0,",",path,") and try again.");
        error();
    );
    counter = 0;
    for(n = 1, #words,
        word = words[n];
        word_level = k_level(word, k);
        coeffs = mat[n,];
        for(m = 1, #coeffs,
            if(coeffs[m] != 0, 
                if(word_level < k_level(pairs[m][1], k), print("Conjecture fails for ",word, " (",k,"-level: ",word_level"), but ",pairs[m][1]," has ",k,"-level ",k_level(pairs[m][1], k)); break());
            );
        );
        counter++;
    );
    if(counter == #words, 
        print(k,"-level conjecture was verified for all ",counter," words of weight ",wt)
    );
};