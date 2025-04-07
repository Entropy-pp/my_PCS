use ark_poly_commit::{Polynomial, LabeledPolynomial, PolynomialCommitment};
use ark_bls12_377::{Bls12_377, Fr};
use ark_poly_commit::kzg10::{Commitment, KZG10, Powers, Randomness, UniversalParams};
use ark_crypto_primitives::sponge::CryptographicSponge;
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr};
use ark_ff::{UniformRand,Field, One, Zero};
use std::ops::Mul;
use ark_std::{test_rng, borrow::Cow};
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial};
use std::time::Instant;
use Mercury::{generate_u, split_u, partial_sum, folded_g, compute_q, compute_s, compute_d, multilinear_eval, pu_evaluate, compute_big_h};
use Mercury::{compute_batch_f_w_l_w_hat, generate_r_i, difference, compute_zs};
type UniPoly_377 = DensePolynomial<<Bls12_377 as Pairing>::ScalarField>;
type PCS = KZG10<Bls12_377, UniPoly_377>;

// TODO: replace by https://github.com/arkworks-rs/crypto-primitives/issues/112.


fn commit(
    pp: &UniversalParams<Bls12_377>,
    fr: &LabeledPolynomial<Fr, DensePolynomial<Fr>>,
) -> (Commitment<Bls12_377>, Randomness<Fr, DensePolynomial<Fr>>) {
    let mut rng = test_rng();
    let f = fr.polynomial();
    let degree = f.degree();
    let srs: Vec<_> = pp
        .powers_of_gamma_g
        .iter()
        .take(degree + 1)
        .map(|(_, g)| *g)
        .collect();

    let powers = Powers {
        powers_of_g: Cow::from(&pp.powers_of_g),
        powers_of_gamma_g: Cow::from(srs),
    };

     PCS::commit(&powers, f, None, Some(&mut rng)).unwrap()
}


fn main() {
    let start = Instant::now();
    let rng = &mut test_rng();

    // setup
    let max_degree = 256;
    let pp = PCS::setup(max_degree, false, rng).unwrap();
    // let vk: VerifierKey<Bls12_377> = VerifierKey {
    //     g: pp.powers_of_g[0],
    //     gamma_g: pp.powers_of_gamma_g[&0],
    //     h: pp.h,
    //     beta_h: pp.beta_h,
    //     prepared_h: pp.prepared_h.clone(),
    //     prepared_beta_h: pp.prepared_beta_h.clone(),
    // };
    // let powers_of_g = pp.powers_of_g[..=max_degree].to_vec();
    // let powers_of_gamma_g = (0..=max_degree)
    //     .map(|i| pp.powers_of_gamma_g[&i])
    //     .collect();
    //
    // let powers = Powers {
    //     powers_of_g: ark_std::borrow::Cow::Owned(powers_of_g),
    //     powers_of_gamma_g: ark_std::borrow::Cow::Owned(powers_of_gamma_g),
    // };


    // secret polynomials, n = 2^{2*t}, b = sqrt(n) = 2^{t}, s = 2*t, degree = n - 1
    // coeffs: coefficients of the secret polynomials
    let base:usize = 2;
    let t:usize = 2;      // 修改这里的 t 来改变多项式的 最高次数!!!!
    let s:usize = 2 * t;
    let n:usize = base.pow(s as u32);
    let degree = n - 1;
    let b:usize = base.pow(t as u32);
    let secret_poly =UniPoly_377::rand(degree, rng);
    // let f: Vec<Fr> = (0..(1 << s)).map(|i| Fr::from(i as u64)).collect(); // 生成 f(i) = i
    // let secret_poly = DensePolynomial::from_coefficients_slice(&f);
    let label = String::from("secret_poly");
    let labeled_poly = LabeledPolynomial::new(
        label.clone(),
        secret_poly.clone(),
        Some(degree),
        Some(2), // we will open a univariate poly at two points
    );
    println!("f(X):");
    println!("{:?}", labeled_poly.polynomial());


    let com_f = commit(&pp, &labeled_poly);
    let u = generate_u(t);
    let (u2, u1) = split_u(&u);
    // 特别注意这里 u2 , u1 的顺序

    // let u :Vec<Fr>= vec![Fr::from(1u64),Fr::from(0u64),Fr::from(1u64),Fr::from(1u64)];
    // let (u2, u1) = split_u(&u);
    println!("{:?}", u);
    println!("{:?}", u1);
    println!("{:?}", u2);
    let v = multilinear_eval(&labeled_poly.coeffs,&u,s);

    // 1. Commiting to partial sum h
    let h_poly = partial_sum(&labeled_poly, &u1);
    println!("h(X):");
    println!("{:?}", h_poly.polynomial());
    let com_h = commit(&pp, &h_poly);
    let hv = multilinear_eval(&h_poly.coeffs,&u2, t);

    // 2. Commiting to folded g
    let alpha:Fr = <Bls12_377 as Pairing>::ScalarField::rand(rng);
    // let alpha = Fr::from(1u64);
    let g_poly = folded_g(&labeled_poly, alpha);
    let q_poly = compute_q(&labeled_poly,alpha);
    println!("g(X):");
    println!("{:?}", g_poly.polynomial());
    println!("q(X):");
    println!("{:?}", q_poly.polynomial());
    let ga = multilinear_eval(&g_poly.coeffs,&u1, t);

    let com_g = commit(&pp, &g_poly);
    let com_q = commit(&pp, &q_poly);

    // 3. Sending proof of correctness for h and degree of g
    let gamma:Fr = <Bls12_377 as Pairing>::ScalarField::rand(rng);
    // let gamma = Fr::from(1u64);
    let s_poly = compute_s(&g_poly,&h_poly,&u1,&u2,gamma,b);
    let com_s = commit(&pp, &s_poly);
    println!("S(X):");
    println!("{:?}", s_poly.polynomial());

    let d_poly = compute_d(&g_poly,b);
    let com_d = commit(&pp, &d_poly);
    println!("D(X):");
    println!("{:?}", d_poly.polynomial());

    // 4. KZG evaluations
    let z:Fr = <Bls12_377 as Pairing>::ScalarField::rand(rng);
    // let z = Fr::from(1u64);
    let z_inverse = z.inverse().expect("z must have an inverse");
    let g_z = g_poly.evaluate(&z);
    let g_hat_z = g_poly.evaluate(&z_inverse);
    let h_z = h_poly.evaluate(&z);
    let h_hat_z = h_poly.evaluate(&z_inverse);
    let s_z = s_poly.evaluate(&z);
    let s_hat_z = s_poly.evaluate(&z_inverse);

    let exponent = (b - 1) as u64;
    let d_z = z.pow([exponent]) * g_hat_z;

    let h_alpha = ( g_z * pu_evaluate(&u1 , z_inverse) + g_hat_z * pu_evaluate(&u1 , z)
        + gamma * ( h_z * pu_evaluate(&u2 , z_inverse) + h_hat_z * pu_evaluate(&u2 , z) - Fr::from(2u64) * v)
        - z * s_z - z_inverse * s_hat_z) / Fr::from(2u64);

    let big_h = compute_big_h(&labeled_poly.polynomial(), &q_poly, z, b, alpha, g_z);
    println!("H(X):");
    println!("{:?}", big_h.polynomial());


    let proof_z = commit(&pp,&big_h);

    let z_b = z.pow([b as u64]);
    let z_b_alpha = z_b - alpha;
    let comm = com_f.0.0.into_group();
    let comm_q = com_q.0.0.into_group();

    let inner = comm - comm_q.mul(z_b_alpha) - &pp.powers_of_g[0].mul(g_z);

    let lhs = Bls12_377::pairing(inner, &pp.h);



    let inner = &pp.beta_h.into_group() - &pp.h.mul(z);  // beta_h - h * point
    let rhs = Bls12_377::pairing(proof_z.0.0.into_group(), inner);



    assert_eq!(lhs , rhs);
    println!("Step f: acc");


    // BDFG20
    let vec_f = vec![g_poly.polynomial(), h_poly.polynomial(), s_poly.polynomial(), d_poly.polynomial()];
    let g_points = vec![z, z_inverse];
    let g_values = vec![g_z, g_hat_z];
    let rr_g = generate_r_i(&g_points, &g_values);

    let h_a = h_poly.evaluate(&alpha);
    let h_points = vec![z, z_inverse, alpha];
    let h_values = vec![h_z, h_hat_z, h_alpha];
    let rr_h = generate_r_i(&h_points, &h_values);

    let s_points = vec![z, z_inverse];
    let s_values = vec![s_z, s_hat_z];
    let rr_s = generate_r_i(&s_points, &s_values);

    let d_zz = d_poly.evaluate(&z);
    let d_points = vec![z];
    let d_values = vec![d_z];
    let rr_d = generate_r_i(&d_points, &d_values);

    let rr = vec![&rr_g, &rr_h, &rr_s, &rr_d];
    let t = vec![z, z_inverse, alpha];
    let all_s = vec![g_points.clone(), h_points.clone(), s_points.clone(), d_points.clone()];

    let batch_z:Fr = <Bls12_377 as Pairing>::ScalarField::rand(rng);
    let batch_gamma:Fr = <Bls12_377 as Pairing>::ScalarField::rand(rng);

    // batch_z, batch_gamma
    let (batch_f, batch_w, batch_l, batch_w_hat) = compute_batch_f_w_l_w_hat(vec_f, rr, t, all_s, batch_gamma, batch_z);

    let comm_batch_w = commit(&pp, &batch_w);

    let comm_batch_w_hat = commit(&pp, &batch_w_hat);



    let vec_com = vec![com_g.0, com_h.0, com_s.0, com_d.0];

    let t = vec![z, z_inverse, alpha];
    let rr = vec![&rr_g, &rr_h, &rr_s, &rr_d];
    let all_s = vec![g_points.clone(), h_points.clone(), s_points.clone(), d_points.clone()];
    let mut re = comm_batch_w_hat.0.0.into_group().mul(batch_z);    // batch_z
    for i in 0..vec_com.len(){
        let gamma_pow_i = batch_gamma.pow([i as u64]);   // batch_gamma
        let s_i = &all_s[i];
        let t_s = difference(&t, s_i);
        let z_s_i = compute_zs(&t_s);
        let scaler = gamma_pow_i.mul(z_s_i.evaluate(&batch_z)); // batch_z
        let scaler_2 = rr[i].evaluate(&batch_z).mul(scaler);    // batch_z
        re = &re + vec_com[i].0.into_group().mul(scaler) - &pp.powers_of_g[0].mul(scaler_2);
    }
    let z_t = compute_zs(&t);
    re = &re - comm_batch_w.0.0.into_group().mul(z_t.evaluate(&batch_z));   // batch_z

    let lhs_2 = Bls12_377::pairing(re, &pp.h);
    let rhs_2 = Bls12_377::pairing(comm_batch_w_hat.0.0.into_group(), &pp.beta_h);

    assert_eq!(lhs_2 , rhs_2);
    println!("Step g: acc");

    // RunTime
    let duration = start.elapsed();
    println!("RunTime: {:?}", duration);


    println!("f(u)  :{:?}", v);
    println!("h(u_2):{:?}", hv);
    println!("g(u_1):{:?}", ga);
    println!("h(a)  :{:?}", h_a);
    println!("v_ha  :{:?}", h_alpha);
}
