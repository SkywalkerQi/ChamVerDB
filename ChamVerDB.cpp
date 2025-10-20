#include <iostream>
#include <stdio.h>
#include <string.h>
#include <fstream>
#include <regex>
#include <openssl/pem.h>
#include <openssl/sha.h>
#include <openssl/rsa.h>
#include <openssl/rand.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/bn.h>
#include <openssl/ssl.h>
#include <gmp.h>
#include <pbc/pbc.h>
#include <gmpxx.h>
#include <unordered_map>
#include <vector>
#include <map>
#include <cmath>
#include <cstring>
#include <sstream>
#include <iomanip>
#include <chrono>
#include <random>
#include <unistd.h>
using namespace std;
int MinCollTimes = 0;
double thebestp = 0;
bool totalflag = false;

// Simulated ReProxyEnc_Key
element_t ga;
element_t rk;

// 计数的变量
double Sum_of_kgen_time = 0;
double Sum_of_enc_time = 0;
double Sum_of_hash_time = 0;
double Sum_of_query_time = 0;
double Sum_of_response_time = 0;
double Sum_of_reconstruct_time = 0;
double Sum_of_Verify_time = 0;

// struct of CH
// ——————————————————————————————————————————————————
struct SK
{
    mpz_class p, pminusone;
    mpz_class q, qminusone;
    mpz_class Lambda, miu; // Paillier sk
    mpz_class N, NSquared, G;
    RSA* RsaSK;
};
struct PK
{
    mpz_class N, NSquared, G;
    RSA* RsaPK;
};
// ——————————————————————————————————————————————————


struct PublicKey
{
    mpz_class N;
    mpz_class g0;
    std::vector<mpz_class> gset;
    mpz_class NSquared;
    pairing_t pairing;
    mpz_class g0_inv;
    element_t g;
    element_t gt;
};
struct PrivateKey
{
    std::vector<mpz_class> x_set;
    mpz_class p;
    mpz_class q;
    mpz_class n;
    std::vector<int> d;
    mpz_class d_mpz;
};
// ——————————————————————————————————————————————————

struct Data
{
    mpz_class c1;
    mpz_class c2;
    element_t c3;
    mpz_class pij;
};

struct QueryKey
{
    PublicKey q_pk;
    PrivateKey q_sk;
};

struct ClientKey
{
    mpz_class d_mpz;
    std::vector<int> d;
    element_t gb;
};

// ——————————————————————————————————————————————————

// strcut of Bucket, one bucket for one row
struct Bucket
{
    std::vector<Data> Datas; // db
    mpz_class HValue; // row chameleon hash value
    mpz_class RValue; // row proof \pi
};

// strcut of DB
struct Database
{
    std::vector<Bucket> Buckets;
    int bucketNum; // the number of bucket
    int bucketCap; // the number of element in each bucket
};
// ——————————————————————————————————————————————————



// ——————————————————————————————————————————————————
Bucket InitializeBucket(int numItems, PublicKey pk)
{
    Bucket bucket;
    bucket.Datas.resize(numItems);
    for (int i = 0; i < numItems; ++i)
    {
        bucket.Datas[i].c1 = mpz_class(-1);
        bucket.Datas[i].c2 = mpz_class(-1);
        element_init_G1(bucket.Datas[i].c3, pk.pairing);
        bucket.Datas[i].pij = mpz_class(-1);
    }
    bucket.HValue = mpz_class(-2);
    bucket.RValue = mpz_class(-3);

    return bucket;
}
Database InitializeDatabase(int numBuckets, int itemsPerBucket, PublicKey pk)
{
    Database db;
    db.Buckets.resize(numBuckets);
    db.bucketNum = numBuckets;
    db.bucketCap = itemsPerBucket;
    for (int i = 0; i < numBuckets; ++i)
        db.Buckets[i] = InitializeBucket(itemsPerBucket, pk);
    return db;
}
Database newMakeDB(PublicKey pk, int dataNum, int dataSize)
{
    const int dimension = dataNum / 2;
    const int d = pow(2, dimension);
    Database db = InitializeDatabase(d, d, pk);
    return db;
}


/*
void PrintDB(Database db) {
    std::cout << " DB - 桶 数量 为: " << std::endl;
    std::cout << db.bucketNum << std::endl;

    std::cout << " DB - 桶 大小 为: " << std::endl;
    std::cout << db.bucketCap << std::endl;

    // std::cout<<" 看看输出: "<<std::endl;
    // std::cout<<sizeof(db.Buckets)<<std::endl;

    // std::cout<<" 看看输出1: "<<std::endl;
    // std::cout<<db.Buckets[0].Datas.capacity()<<std::endl;

    // std::cout<<" 看看输出2: "<<std::endl;
    // std::cout<<db.Buckets[0].Datas.size()<<std::endl;

    // std::cout<<" 看看输出3: "<<std::endl;
    // std::cout<<sizeof(db.Buckets[0].Datas.size()/sizeof(db.Buckets[0].Datas))<<std::endl;

    std::cout << " 桶内所有元素为: \n" << std::endl;
    for (int i = 0; i < db.bucketNum; i++) { // 对每个桶
        for (int j = 0; j < db.bucketCap; j++) {// 这里指向的是指针, 明天看看怎么改
            Bucket tempb = db.Buckets[i];
            gmp_printf("对于第%d个桶中第%d个元素: DB_Value=%Zd, DB_HValue=%Zd, DB_RValue=%Zd\n",
                i, j, tempb.Datas[j].DataValue, tempb.Datas[j].HValue, tempb.Datas[j].RValue);
        }
    }
}
*/


void init_pairing(pairing_t pairing, int lambda)
{
    char param[1024];
    pbc_param_t par;
    pbc_param_init_a_gen(par, lambda, 160); // rbits = lambda, qbits =160;
    // 将参数输出到字符串缓冲区
    FILE* fp = fmemopen(param, sizeof(param), "w");
    if (!fp)
    {
        cerr << "Failed to open memory stream for param" << endl;
        exit(1);
    }
    pbc_param_out_str(fp, par);
    fclose(fp);
    pairing_init_set_buf(pairing, param, strlen(param));
    pbc_param_clear(par);
}

// Compute log2
int Log2(const mpz_class& x)
{
    // 将大整数转为浮点数
    double bn = mpz_get_d(x.get_mpz_t());
    // 计算对数值并返回
    return static_cast<int>(std::log2(bn));
}

// Convert mpz to binary vector
std::vector<int> intToBinary(const mpz_class& n)
{
    std::vector<int> bins;
    unsigned int bits = mpz_sizeinbase(n.get_mpz_t(), 2); // 获取二进制位数

    for (unsigned int i = 0; i < bits; i++)
    {
        // 从高位到低位获取每一位
        int bit = mpz_tstbit(n.get_mpz_t(), bits - i - 1);
        bins.push_back(bit);
    }

    return bins;
}
// Compute x^2 mod N
mpz_class quadraticResidue(const mpz_class& x, const mpz_class& N)
{
    return (x * x) % N;
}

void genXnG(int l, const mpz_class& N, std::vector<mpz_class>& x_set, std::vector<mpz_class>& g_set)
{
    gmp_randstate_t state;
    gmp_randinit_mt(state);

    std::random_device rd;
    auto now = std::chrono::high_resolution_clock::now();
    uint64_t seed = rd() ^ std::chrono::duration_cast<std::chrono::nanoseconds>(now.time_since_epoch()).count();
    gmp_randseed_ui(state, seed);

    for (int i = 0; i < l; i++)
    {
        mpz_class x;
        mpz_urandomm(x.get_mpz_t(), state, N.get_mpz_t());
        mpz_class g = quadraticResidue(x, N);
        x_set.push_back(x);
        g_set.push_back(g);
    }
    gmp_randclear(state);
}

/*
void printgg(std::vector<mpz_class> &gg)
{
    int l = gg.size();
    std::cout << "gg数组的大小为" << l << std::endl;
    for (int i = 0; i < l; i++)
    {
        std::cout << "which？" << i << std::endl;
        gmp_printf("gg数组中第%Zd个元素为%Zd\n", i, gg[i]);
    }
}
*/


// ——————————————————————————————————————————————————
// Generate a large prime number with the specified number of digits
mpz_class genLargePrime(int bits)
{
    gmp_randclass rr(gmp_randinit_mt);
    rr.seed(time(NULL));
    mpz_class prime_candidate = rr.get_z_bits(bits);
    mpz_nextprime(prime_candidate.get_mpz_t(), prime_candidate.get_mpz_t());
    return prime_candidate;
}


struct CheckValue
{
    mpz_class h;
    mpz_class r;
};


mpz_class innerHash(const mpz_class& m, const mpz_class& r, const mpz_class& N)
{
    return m + r % N;
}


// 计算满足 g^x = h mod p 的 x, 输入: down, up, modular
mpz_class findLog(const mpz_class& g, const mpz_class& h, const mpz_class& p)
{
    // mpz_class g("15267");
    // mpz_class h("233081289");
    // mpz_class p("45778392193");
    mpz_class m, gm, g_inv, g_inv_m;

    mpz_class p_minus_1 = p - 1;
    double p_val = p_minus_1.get_d();
    double sqrt_val = std::sqrt(p_val); // 使用 std::sqrt
    m = mpz_class(std::ceil(sqrt_val)); // 使用 std::ceil

    mpz_class p_minus_2 = p - 2; // 先计算 p-2
    mpz_powm(gm.get_mpz_t(), g.get_mpz_t(), m.get_mpz_t(), p.get_mpz_t());
    mpz_powm(g_inv.get_mpz_t(), g.get_mpz_t(), p_minus_2.get_mpz_t(), p.get_mpz_t());
    mpz_powm(g_inv_m.get_mpz_t(), g_inv.get_mpz_t(), m.get_mpz_t(), p.get_mpz_t());

    // 修改为使用 map
    std::map<mpz_class, mpz_class> baby_steps;
    mpz_class one(1);
    mpz_class temp = one;
    for (mpz_class i = 0; i < m; ++i)
    {
        baby_steps[temp] = i;
        temp = (temp * g) % p;
    }

    // Giant Steps
    mpz_class y = h;
    for (mpz_class i = 0; i < m; ++i)
    {
        if (baby_steps.find(y) != baby_steps.end())
        {
            mpz_class result = i * m + baby_steps[y];
            return result.get_si(); // 转换为 long int
        }
        y = (y * g_inv_m) % p;
    }
    // gmp_printf("h is %Zd\n\n",h);
    // std::cout<< "?" <<std::endl;
    return -1;
}
// ---------------------------求对数的函数----------——----------------

//                           变色龙哈希部分
// ————————————————————————————————————————————————————————————————————————————————————————————————————

//
// 生成RSA密钥对
RSA* generateRSAKeyPair(int bits)
{
    RSA* rsa = RSA_new();
    BIGNUM* bn = BN_new();
    BN_set_word(bn, RSA_F4); // 将公钥设置为0x10001L
    if (RSA_generate_key_ex(rsa, bits, bn, nullptr) != 1)
    { // 创建RSA密钥,成功则返回1
        RSA_free(rsa);
        std::cerr << "生成RSA密钥对失败" << std::endl;
        return nullptr;
    }
    // std::cout << "RSA密钥生成成功" << std::endl;
    return rsa;
}

mpz_class getPrime(int bits)
{
    gmp_randstate_t grt;
    gmp_randinit_default(grt);
    gmp_randseed_ui(grt, clock());
    // p、q初始化
    mpz_class p, q;
    // p、q的范围在0~2^128-1
    mpz_urandomb(p.get_mpz_t(), grt, bits); // 位数
    // 生成p, q大素数
    mpz_nextprime(p.get_mpz_t(), p.get_mpz_t());
    // 判断生成的是否是素数得到的结果为2则确定为大素数
    int su2 = mpz_probab_prime_p(p.get_mpz_t(), 10);
    return p;
}

// 变色龙哈希密钥生成算法
void CHKG(SK& privKey, PK& pubKey)
{
    // 初始化openssl
    OpenSSL_add_all_algorithms();
    ERR_load_ERR_strings();

    // 生成rsa密钥
    RSA* rsa = generateRSAKeyPair(512); // 1024
    if (rsa == nullptr)
    {
        std::cerr << "RSA密钥生成失败" << std::endl;
        return;
    }
    // 复制RSA密钥
    privKey.RsaSK = RSAPrivateKey_dup(rsa);
    pubKey.RsaPK = RSAPublicKey_dup(rsa);
    if (!privKey.RsaSK || !pubKey.RsaPK)
    {
        std::cerr << "RSA密钥复制失败" << std::endl;
        RSA_free(rsa);
        return;
    }
    RSA_free(rsa);

    // std::cout << privKey.RsaSK << std::endl;
    // std::cout << pubKey.RsaPK << std::endl;

    // 随机数生成阶段
    // ——————————————————————————————————————————————————————————
    // 设置随机数种子
    gmp_randstate_t grt;
    gmp_randinit_default(grt);
    gmp_randseed_ui(grt, clock());
    // p、q初始化
    mpz_class p, q, p1, q1;
    // p、q的范围在0~2^128-1
    mpz_urandomb(p.get_mpz_t(), grt, 128); // 原来是128
    mpz_urandomb(q.get_mpz_t(), grt, 128); // 原来是128
    // 生成p, q大素数
    mpz_nextprime(p.get_mpz_t(), p.get_mpz_t());
    mpz_nextprime(q.get_mpz_t(), q.get_mpz_t());
    // 判断生成的是否是素数得到的结果为2则确定为大素数
    int su2 = mpz_probab_prime_p(q.get_mpz_t(), 10);
    int su1 = mpz_probab_prime_p(p.get_mpz_t(), 10);
    p1 = p - 1;
    q1 = q - 1;
    // ——————————————————————————————————————————————————————————

    privKey.p = p;
    privKey.q = q;
    privKey.pminusone = p1;
    privKey.qminusone = q1;
    privKey.N = p * q;
    privKey.NSquared = privKey.N * privKey.N;
    privKey.G = privKey.N + 1;
    pubKey.N = privKey.N;
    pubKey.NSquared = privKey.NSquared;
    pubKey.G = privKey.G;
    // privKey.Lambda = (p-1)*(q-1);

    // Lambda的计算过程
    mpz_lcm(privKey.Lambda.get_mpz_t(), p1.get_mpz_t(), q1.get_mpz_t());

    // miu的计算过程

    mpz_class t_miu;
    mpz_powm(t_miu.get_mpz_t(), privKey.G.get_mpz_t(), privKey.Lambda.get_mpz_t(), privKey.NSquared.get_mpz_t());
    t_miu = (t_miu - 1) / privKey.N;
    // 取逆
    mpz_invert(privKey.miu.get_mpz_t(), t_miu.get_mpz_t(), privKey.N.get_mpz_t());

    // std::cout << "变色龙哈希密钥生成完毕！"<< std::endl;

    // std::cout<< "**************************** 输出密钥参数 ****************************" << std::endl;
    // std::cout<< "*————————————————— 私钥 —————————————————" << std::endl;
    // gmp_printf("参数中的 privKey.G = %Zd\n\n", privKey.G);
    // gmp_printf("参数中的 privKey.N = %Zd\n\n", privKey.N);
    // gmp_printf("参数中的 privKey.NSquared = %Zd\n\n", privKey.NSquared);
    // gmp_printf("参数中的 privKey.lambda = %Zd\n\n", privKey.Lambda);
    // gmp_printf("参数中的 privKey.miu = %Zd\n\n", privKey.miu);
    // std::cout<< "*————————————————— 公钥 —————————————————" << std::endl;
    // gmp_printf("参数中的 pubKey.G = %Zd\n\n", pubKey.G);
    // gmp_printf("参数中的 pubKey.N = %Zd\n\n", pubKey.N);
    // gmp_printf("参数中的 pubKey.NSquared = %Zd\n\n", pubKey.NSquared);
    // std::cout<< "********************************************************************" << std::endl;
}

// 变色龙哈希计算函数，生成的是校验对
CheckValue* CHHash(PK& pubKey, const mpz_class& m)
{
    unsigned char rand_bytes[64];
    if (RAND_bytes(rand_bytes, sizeof(rand_bytes)) != 1)
    {
        std::cerr << "随机数生成失败!" << std::endl;
        return nullptr;
    }
    CheckValue* cv = new CheckValue(); // 结构体要初始化,不然会
    mpz_class r, K;
    mpz_import(r.get_mpz_t(), sizeof(rand_bytes), 1, 1, 0, 0, rand_bytes);
    r = r % pubKey.N;
    mpz_import(K.get_mpz_t(), sizeof(rand_bytes), 1, 1, 0, 0, rand_bytes);
    K = K % pubKey.N;

    cv->r = r;

    mpz_class enc_r, rem, re, gre, kn, h;
    const BIGNUM* n = nullptr, * e = nullptr;
    RSA_get0_key(pubKey.RsaPK, &n, &e, nullptr);

    // 将BIGNUM转换为 mpz_class
    char* e_str = BN_bn2dec(e);
    char* n_str = BN_bn2dec(n);

    mpz_class e_mpz(e_str), n_mpz(n_str);
    OPENSSL_free(e_str);
    OPENSSL_free(n_str);

    // ----------------------------------------测试CH哈希时间----------------------------------------
    clock_t start_hash = clock();

    /*
    // --------------------------------------------------测试代码
    // 要计算g^H(m)·g^(r^e)·K^N mod N^2
    // 先计算r^e
    mpz_powm(re.get_mpz_t(), r.get_mpz_t(), e_mpz.get_mpz_t(), n_mpz.get_mpz_t());
    // gmp_printf("********** 对比检查1 ********** : re_1 = %Zd\n\n",re);
    // 再计算g^(r^e)
    mpz_powm(gre.get_mpz_t(), pubKey.G.get_mpz_t(), re.get_mpz_t(), pubKey.NSquared.get_mpz_t());
    // gmp_printf("********** 对比检查2 ********** : gre_1 = %Zd\n\n",gre);
    // 再计算 g^h
    mpz_powm(gh.get_mpz_t(), pubKey.G.get_mpz_t(), m.get_mpz_t(), pubKey.NSquared.get_mpz_t());
    // gmp_printf("********** 对比检查3 ********** : gh_1 = %Zd\n\n",gh);
    */
    // --------------------------------------------------测试代码
    // 要计算g^H(m)·g^(r^e)·K^N mod N^2
    // 先计算r^e
    mpz_powm(re.get_mpz_t(), r.get_mpz_t(), e_mpz.get_mpz_t(), n_mpz.get_mpz_t());
    // gmp_printf("********** 对比检查1 ********** : re_1 = %Zd\n\n",re);

    // 再计算 r^e+m
    rem = re + m % pubKey.NSquared;

    // 再计算g^(r^e+m)
    // gmp_printf("********** 对比检查2 ********** : gre_1 = %Zd\n\n",gre);
    mpz_powm(gre.get_mpz_t(), pubKey.G.get_mpz_t(), rem.get_mpz_t(), pubKey.NSquared.get_mpz_t());

    // *************************
    // K = innerHash(m, r, pubKey.N);
    // *************************

    // 再计算 K^n
    // mpz_powm(kn.get_mpz_t(), K.get_mpz_t(), pubKey.N.get_mpz_t(), pubKey.NSquared.get_mpz_t());
    // gmp_printf("********** 对比检查4 ********** : kn_1 = %Zd\n\n",kn);

    // h = (gh * gre * kn) % pubKey.NSquared;
    // h = (gh * gre) % pubKey.NSquared;

    h = gre;
    // --------------------------------------------------测试代码
    clock_t end_hash = clock();
    double duration_hash = (end_hash - start_hash) * 1000.0 / CLOCKS_PER_SEC;
    // std::cout<< "time of single HASH is " <<duration_hash<<std::endl;
    Sum_of_hash_time += duration_hash;
    // ----------------------------------------测试CH哈希时间----------------------------------------

    cv->h = h;
    // std::cout << "哈希计算完成" << std::endl;
    // gmp_printf("r = %Zd\n\n", r);
    // gmp_printf("h = %Zd\n\n", h);
    return cv;
}

// 变色龙哈希的一致性检验函数, CHCheck是会出错的, 原因还没找到
bool CHCheck(PK& pubKey, const mpz_class& m, const mpz_class& h, const mpz_class& r)
{

    cout << "进入CHCheck函数了嘛?" << endl;
    bool flag;
    flag = false;

    // 选取随机的k
    unsigned char rand_bytes[128];
    if (RAND_bytes(rand_bytes, sizeof(rand_bytes)) != 1)
    {
        std::cerr << "随机数生成失败!" << std::endl;
        return flag;
    }
    mpz_class K;
    mpz_import(K.get_mpz_t(), sizeof(rand_bytes), 1, 1, 0, 0, rand_bytes);
    K = K % pubKey.N;
    //


    int rsa_size = RSA_size(pubKey.RsaPK);
    unsigned char* encrypted = new unsigned char[rsa_size];
    unsigned char* input = (unsigned char*)mpz_get_str(nullptr, 16, r.get_mpz_t());


    size_t input_len = strlen((char*)input);
    if (input_len > static_cast<size_t>(rsa_size - 42))
    {
        input_len = rsa_size - 42;
    }

    mpz_class enc_r, computed_h, re, gre, gh, kn;


    const BIGNUM* n = nullptr, * e = nullptr;
    RSA_get0_key(pubKey.RsaPK, &n, &e, nullptr);
    char* e_str = BN_bn2dec(e);
    char* n_str = BN_bn2dec(n);
    mpz_class e_mpz(e_str), n_mpz(n_str);
    OPENSSL_free(e_str);
    OPENSSL_free(n_str);

    mpz_powm(re.get_mpz_t(), r.get_mpz_t(), e_mpz.get_mpz_t(), n_mpz.get_mpz_t());
    mpz_powm(gre.get_mpz_t(), pubKey.G.get_mpz_t(), re.get_mpz_t(), pubKey.NSquared.get_mpz_t());
    mpz_powm(gh.get_mpz_t(), pubKey.G.get_mpz_t(), m.get_mpz_t(), pubKey.NSquared.get_mpz_t());
    K = innerHash(m, r, pubKey.N);
    mpz_powm(kn.get_mpz_t(), K.get_mpz_t(), pubKey.N.get_mpz_t(), pubKey.NSquared.get_mpz_t());
    computed_h = (gh * gre * kn) % pubKey.NSquared;
    if (computed_h == h)
    {
        std::cout << "Check通过！" << std::endl;
        flag = true;
    }
    return flag;
}

CheckValue* CHAdapt(PK& pubKey, SK& privKey, const mpz_class& m, const mpz_class& new_m, const mpz_class& h, const mpz_class& r)
{

    CheckValue* cv = new CheckValue(); // 结构体要初始化, 不然会报错
    mpz_class new_r, K;

    mpz_class enc_r;
    const BIGNUM* n = nullptr, * e = nullptr, * d = nullptr;
    RSA_get0_key(pubKey.RsaPK, &n, &e, nullptr);
    RSA_get0_key(privKey.RsaSK, &n, &d, nullptr);

    char* e_str = BN_bn2dec(e);
    char* d_str = BN_bn2dec(d);
    char* n_str = BN_bn2dec(n);

    mpz_class e_mpz(e_str), d_mpz(d_str), n_mpz(n_str);
    OPENSSL_free(e_str);
    OPENSSL_free(d_str);
    OPENSSL_free(n_str);
    mpz_class re;
    mpz_powm(re.get_mpz_t(), r.get_mpz_t(), e_mpz.get_mpz_t(), n_mpz.get_mpz_t());
    mpz_class tempres_r = m + re - new_m;
    mpz_powm(new_r.get_mpz_t(), tempres_r.get_mpz_t(), d_mpz.get_mpz_t(), n_mpz.get_mpz_t());
    cv->r = r;

    std::cout << "凭证变更完成！" << std::endl;
    gmp_printf("r = %Zd\n\n", cv->r);
    gmp_printf("h = %Zd\n\n", cv->h);
    return cv;
}


static mpz_class bytes_to_mpz(const uint8_t* data, size_t len)
{
    mpz_class z;
    mpz_import(z.get_mpz_t(), len, 1, 1, 0, 0, data);
    return z;
}

// -------------- 哈希到 N^2 互素元素 -------------------
mpz_class H2_GT_to_ZN2(element_t gt, mpz_class N2)
{
    const size_t nb = SHA512_DIGEST_LENGTH;
    uint8_t buf[nb];
    std::vector<unsigned char> gt_bytes;

    int ele_len = element_length_in_bytes(gt);
    gt_bytes.resize(ele_len);

    element_to_bytes(gt_bytes.data(), gt);

    SHA512(gt_bytes.data(), gt_bytes.size(), buf);

    mpz_class t = bytes_to_mpz(buf, nb) % N2;
    if (t == 0)
        t = 1;

    mpz_class g;
    mpz_gcd(g.get_mpz_t(), t.get_mpz_t(), N2.get_mpz_t());

    while (g != 1)
    {
        t = (t + 1) % N2;
        if (t == 0)
            t = 1;
        mpz_gcd(g.get_mpz_t(), t.get_mpz_t(), N2.get_mpz_t());
    }
    return t;
}

QueryKey KeyGen(int bits)
{
    QueryKey qk;
    mpz_class p, q, n, n2, d;
    p = getPrime(bits / 2);
    q = getPrime(bits / 2);
    n = p * q;
    n2 = n * n;
    int l = Log2(n);
    d = getPrime(l);
    qk.q_sk.d_mpz = d;
    std::vector<int> binary_d = intToBinary(d);
    std::vector<mpz_class> g_set, x_set;
    genXnG(l, n, g_set, x_set);

    mpz_class MulSum = 1;
    for (int i = 0; i < l; i++)
    {
        mpz_class temp;
        mpz_class exponential(binary_d[i]);
        mpz_powm(temp.get_mpz_t(), g_set[i].get_mpz_t(), exponential.get_mpz_t(), n2.get_mpz_t());
        MulSum = MulSum * temp % n2;
    }
    mpz_class g0_inv;
    mpz_invert(g0_inv.get_mpz_t(), MulSum.get_mpz_t(), n2.get_mpz_t());
    qk.q_pk.g0 = MulSum;
    qk.q_pk.gset = g_set;
    qk.q_pk.N = n;
    qk.q_pk.NSquared = n2;
    qk.q_pk.g0_inv = g0_inv;

    init_pairing(qk.q_pk.pairing, 512);
    element_init_G1(qk.q_pk.g, qk.q_pk.pairing);
    element_init_GT(qk.q_pk.gt, qk.q_pk.pairing);
    element_random(qk.q_pk.g);
    element_random(qk.q_pk.gt);
    qk.q_sk.d = binary_d;
    qk.q_sk.n = n;
    qk.q_sk.p = p;
    qk.q_sk.q = q;
    qk.q_sk.x_set = x_set;
    return qk;
}

ClientKey KeyGen_4_Client(QueryKey qk)
{
    ClientKey ck;
    int l = Log2(qk.q_pk.N);
    mpz_class d = getPrime(l);
    ck.d_mpz = d;
    ck.d = intToBinary(d);
    element_init_G1(ck.gb, qk.q_pk.pairing);
    element_pow_mpz(ck.gb, qk.q_pk.g, ck.d_mpz.get_mpz_t());
    return ck;
}

void KVWrite(int dataNum, int dataSize)
{
    std::string fileName = "DbFile_" + std::to_string(dataNum) + "_" + std::to_string(dataSize) + ".txt";
    std::ofstream file(fileName);
    if (!file.is_open())
    {
        std::cerr << "无法创建文件: " << fileName << std::endl;
        return;
    }
    gmp_randstate_t rand_state;
    gmp_randinit_default(rand_state);
    gmp_randseed_ui(rand_state, time(nullptr)); 

    mpz_class max_value;
    mpz_ui_pow_ui(max_value.get_mpz_t(), 2, dataSize);
    int total_datanum = pow(2, dataNum);
    for (int i = 1; i <= total_datanum; ++i)
    {
        std::string key = std::to_string(i);
        mpz_class value;
        mpz_urandomm(value.get_mpz_t(), rand_state, max_value.get_mpz_t());

        file << key << ":" << value.get_str() << "\n";
    }
    gmp_randclear(rand_state);
    file.close();

    std::cout << "'数据集'生成完毕..." << std::endl;
    std::cout << "写入地址为 " << fileName << std::endl;
}

void KVRead(const std::string& fileName /*, Database& db, int dataNum*/)
{
    std::cout << "------------" << std::endl;
    std::cout << "进入读文件函数" << std::endl;
    std::ifstream file(fileName);
    if (!file.is_open())
    {
        std::cerr << "文件 " << fileName << " 不存在, 请先创建文件..." << std::endl;
        // return db;
    }
    int CollCnt = 0;
    int cnt = 1;
    std::string line;
    std::regex number_regex("\\d+");
    while (std::getline(file, line))
    {
        size_t pos = line.find(":");
        if (pos != std::string::npos)
        {
            std::string keyPart = line.substr(0, pos);
            std::string valuePart = line.substr(pos + 1);
            std::cout << "key: " << keyPart << std::endl;
            std::cout << "value: " << valuePart << std::endl;
        }
    }
    if (file.bad())
    {
        std::cerr << "读取文件时出错" << std::endl;
    }
}

struct ParitySet
{
    std::vector<mpz_class> pi;
};

void DataEnc(PrivateKey sk, PublicKey pk, mpz_class mpzvalue, mpz_class c1, mpz_class c2, element_t c3, int cnt, int d)
{
    element_t r, k;
    element_init_Zr(r, pk.pairing);
    element_init_Zr(k, pk.pairing);
    element_random(r);
    element_random(k);

    element_t gtr;
    element_init_GT(gtr, pk.pairing);
    element_pow_zn(gtr, pk.gt, r);

    mpz_class h2 = H2_GT_to_ZN2(gtr, pk.NSquared);
    element_t z, zk;
    element_init_GT(z, pk.pairing);
    element_init_GT(zk, pk.pairing);

    pairing_apply(z, pk.g, pk.g, pk.pairing);
    element_pow_zn(zk, z, k);

    mpz_class third_part, first_part, nplus1 = pk.N + 1;
    element_t gtr_zk;
    element_init_GT(gtr_zk, pk.pairing);
    element_mul(gtr_zk, gtr, zk);

    mpz_powm(third_part.get_mpz_t(), nplus1.get_mpz_t(), mpzvalue.get_mpz_t(), pk.NSquared.get_mpz_t());
    first_part = pk.g0_inv;
    c1 = first_part * h2;
    c1 = c1 * third_part;

    mpz_class gtr_zk_mpz;
    element_to_mpz(gtr_zk_mpz.get_mpz_t(), gtr_zk);
    c2 = gtr_zk_mpz;


    element_t gak;
    element_init_G1(gak, pk.pairing);
    element_pow_zn(gak, ga, k); 
    element_init_G1(c3, pk.pairing);
    element_set(c3, gak);
   
    element_clear(r);
    element_clear(k);
    element_clear(gtr);
    element_clear(z);
    element_clear(zk);
    element_clear(gak);
}

Database EncWholeDataset(PrivateKey sk, PublicKey pk, PK chpk, const std::string& fileName, Database& db, int dataNum, ParitySet ps)
{
    std::cout << "------------" << std::endl;
    std::cout << "EncWholeDataset函数" << std::endl;
    std::ifstream file(fileName);
    if (!file.is_open())
    {
        std::cerr << "文件 " << fileName << " 不存在, 请先创建文件..." << std::endl;
    }
    int cnt = 0;
    std::string line;
    std::regex number_regex("\\d+");
    int d = db.bucketNum;
    mpz_class xorTemp(0);
    ps.pi.resize(d);
    while (std::getline(file, line))
    {
        size_t pos = line.find(":");
        if (pos != std::string::npos)
        {
            std::string keyPart = line.substr(0, pos);
            std::string valuePart = line.substr(pos + 1);
            mpz_class mpzkey(keyPart), mpzvalue;
            mpzvalue.set_str(valuePart, 16);

            db.Buckets[cnt / d].Datas[cnt % d].pij = mpzvalue; 
            // Sum of Xor
            mpz_xor(xorTemp.get_mpz_t(), xorTemp.get_mpz_t(), mpzvalue.get_mpz_t());
            mpz_class ct1 = 0, ct2 = 0;

            clock_t start_enc = clock();
            DataEnc(sk, pk, mpzvalue, ct1, ct2, db.Buckets[cnt / d].Datas[cnt % d].c3, cnt, d);
            clock_t end_enc = clock();
            double duration_enc = (end_enc - start_enc) * 1000.0 / CLOCKS_PER_SEC;
            Sum_of_enc_time += duration_enc;
            db.Buckets[cnt / d].Datas[cnt % d].c1 = ct1; 
            db.Buckets[cnt / d].Datas[cnt % d].c2 = ct2; 
            if (cnt % d == d - 1)
            { // 搞完一个桶了
                for (int j = 0; j < d; j++)
                {
                    mpz_xor(db.Buckets[cnt / d].Datas[j].pij.get_mpz_t(), db.Buckets[cnt / d].Datas[j].pij.get_mpz_t(), xorTemp.get_mpz_t());
                }
                CheckValue* cv = CHHash(chpk, xorTemp);
                db.Buckets[cnt / d].HValue = cv->h;
                db.Buckets[cnt / d].RValue = cv->r;
                ps.pi[cnt / d] = xorTemp;
                xorTemp = 0;
            }
            cnt++;
        }
    }
    if (file.bad())
    {
        std::cerr << "读取文件时出错" << std::endl;
    }
    return db;
}

//  One-hot vector, is same as select one row
std::pair<std::vector<int>, std::vector<int>> QueryGen(Database db, int k)
{
    std::vector<int> q1, q2;
    q1.resize(db.bucketCap);
    q2.resize(db.bucketCap + 1);
    for (int i = 0; i < db.bucketCap; i++)
    {
        q1[i] = 0;
        q2[i] = 0;
    }
    q1[k / db.bucketCap] = 1;
    q2[k % db.bucketCap] = 1;
    q2[db.bucketCap] = 1;
    return std::make_pair(q1, q2);
}

Bucket Answer(std::vector<int> q, Database db)
{
    int ind = 0;
    for (ind = 0; ind < q.size(); ind++)
    {
        if (q[ind] == 1)
            break;
    }
    return db.Buckets[ind];
}

mpz_class DataRecovery(Bucket Ans, PrivateKey privKey, PublicKey pubKey, ClientKey ck, int key)
{
    clock_t start_innerDR = clock();
    Data ans = Ans.Datas[key % Ans.Datas.size()];

    mpz_class pij;
    pij = ans.pij;

    element_t alpha;
    element_init_Zr(alpha, pubKey.pairing);

    element_t ga_alpha, c3_p;
    element_init_G1(ga_alpha, pubKey.pairing);
    element_init_G1(c3_p, pubKey.pairing);
    element_mul(c3_p, ans.c3, ga_alpha);

    element_t c3_pp;
    element_init_GT(c3_pp, pubKey.pairing);
    pairing_apply(c3_pp, rk, c3_p, pubKey.pairing);

    element_t z, c2_p;
    element_init_GT(z, pubKey.pairing);
    pairing_apply(z, pubKey.g, pubKey.g, pubKey.pairing);
    element_pow_zn(z, z, alpha);
    element_init_GT(c2_p, pubKey.pairing);
    element_mul_mpz(c2_p, z, ans.c2.get_mpz_t());

    element_t c3_pp_inv;
    element_init_GT(c3_pp_inv, pubKey.pairing);
    element_invert(c3_pp_inv, c3_pp);

    mpz_class d_inv;
    mpz_invert(d_inv.get_mpz_t(), ck.d_mpz.get_mpz_t(), pubKey.NSquared.get_mpz_t());

    element_pow_mpz(c3_pp_inv, c3_pp_inv, d_inv.get_mpz_t());
    element_t gtr;
    element_init_GT(gtr, pubKey.pairing);
    element_mul(gtr, c2_p, c3_pp_inv);

    mpz_class part2;
    part2 = H2_GT_to_ZN2(gtr, pubKey.NSquared);

    mpz_class frac = ans.c1 * part2 * pubKey.g0;
    mpz_div(frac.get_mpz_t(), frac.get_mpz_t(), pubKey.N.get_mpz_t());
    mpz_mod(frac.get_mpz_t(), frac.get_mpz_t(), pubKey.N.get_mpz_t());

    element_clear(alpha);
    element_clear(ga_alpha);
    element_clear(c3_p);
    element_clear(c3_pp);
    element_clear(z);
    element_clear(c2_p);
    element_clear(c3_pp_inv);
    element_clear(gtr);
    clock_t end_innerDR = clock();
    double duration_innerDR = (end_innerDR - start_innerDR) * 1000.0 / CLOCKS_PER_SEC;

    Sum_of_reconstruct_time += duration_innerDR;
    return frac;
}

bool DataVerification(mpz_class d, Bucket Ans, PK chpk, int key) {
    clock_t start_V = clock();
    bool flag = false;

    // get data tuple
    Data ans = Ans.Datas[key % Ans.Datas.size()];

    // get chameleon hash value
    mpz_class pi;
    mpz_xor(pi.get_mpz_t(), ans.pij.get_mpz_t(), d.get_mpz_t());
    flag = CHCheck(chpk, pi, Ans.HValue, Ans.RValue);

    clock_t end_V = clock();
    double duration_V = (end_V - start_V) * 1000.0 / CLOCKS_PER_SEC;
    Sum_of_Verify_time += duration_V;
    return flag;
}


void schemeTest(int dataNum, int dataSize)
{
    int WantToSearch = 6;

    std::cout << "\n开始执行方案测试, 当前数据量为 " << dataNum << std::endl;

    SK privKey;
    PK pubKey;

    clock_t start_kgen = clock();

    CHKG(privKey, pubKey);
    QueryKey qk = KeyGen(1024);
    ClientKey ck = KeyGen_4_Client(qk);
    element_init_G1(rk, qk.q_pk.pairing);
    mpz_class a_inv;
    mpz_invert(a_inv.get_mpz_t(), qk.q_sk.d_mpz.get_mpz_t(), qk.q_pk.NSquared.get_mpz_t());
    element_pow_mpz(rk, ck.gb, a_inv.get_mpz_t());
    element_init_G1(ga, qk.q_pk.pairing);
    element_pow_mpz(ga, qk.q_pk.g, qk.q_sk.d_mpz.get_mpz_t());

    clock_t end_kgen = clock();
    double duration_kgen = (end_kgen - start_kgen) * 1000.0 / CLOCKS_PER_SEC;
    Sum_of_kgen_time += duration_kgen;
    std::cout << " \n密钥生成完毕 " << std::endl;

    ParitySet ps;

    Database db = newMakeDB(qk.q_pk, dataNum, dataSize);
    std::cout << " \n数据库创建完毕 " << std::endl;
    std::string fileName = "DbFile_" + std::to_string(dataNum) + "_" + std::to_string(dataSize) + ".txt";
    std::ofstream testFile("test.txt");
    if (!testFile)
    {
        std::cerr << "无法创建 test.txt!" << std::endl;
    }
    testFile.close();
    std::cout << " \n准备加密数据库完毕 " << std::endl;
    db = EncWholeDataset(qk.q_sk, qk.q_pk, pubKey, fileName, db, dataNum, ps);

    clock_t start_query = clock();
    std::vector<int> q1 = QueryGen(db, WantToSearch).first;
    std::vector<int> q2 = QueryGen(db, WantToSearch).second;
    clock_t end_query = clock();
    double duration_query = (end_query - start_query) * 1000.0 / CLOCKS_PER_SEC;
    Sum_of_query_time += duration_query;

    clock_t start_response = clock();
    Bucket ans = Answer(q1, db);
    clock_t end_response = clock();
    double duration_response = (end_response - start_response) * 1000.0 / CLOCKS_PER_SEC;
    Sum_of_response_time += duration_response;

    clock_t start_m_test = clock();
    for (int i = 0; i < q1.size(); i++)
    {
        mpz_class qi(q1[i]);
        mpz_class multiplication = qi * ans.Datas[WantToSearch % ans.Datas.size()].c1;
    }
    clock_t end_m_test = clock();
    double duration_m_test = (end_m_test - start_m_test) * sqrt(dataNum) * 1000.0 / CLOCKS_PER_SEC;
    std::cout << "向量-矩阵 哈达玛积操作耗时 is " << duration_m_test << std::endl;


    mpz_class finalData;
    finalData = DataRecovery(ans, qk.q_sk, qk.q_pk, ck, WantToSearch);
    DataVerification(finalData, ans, pubKey, WantToSearch);

}

// Scheme Test Function
void ourTest()
{
    for (int i = 8; i <= 20; i += 2)
    {
        schemeTest(i, 32);
        // Sum_of_hash_time = sqrt(Sum_of_hash_time);
        std::cout << " 密钥生成用时------------: " << Sum_of_kgen_time << std::endl;
        std::cout << " 加密用时------------: " << Sum_of_enc_time << std::endl;
        std::cout << " 哈希用时------------: " << Sum_of_hash_time << std::endl;
        std::cout << " OFFLINE阶段总共用时------------: " << Sum_of_kgen_time + Sum_of_enc_time + Sum_of_hash_time << std::endl;
        std::cout << " 查询用时------------: " << Sum_of_query_time << std::endl;
        std::cout << " 响应用时------------: " << Sum_of_response_time << std::endl;
        std::cout << " 重构用时------------: " << Sum_of_reconstruct_time << std::endl;
        std::cout << " 验证用时------------: " << Sum_of_Verify_time << std::endl;
        Sum_of_kgen_time = 0;
        Sum_of_enc_time = 0;
        Sum_of_hash_time = 0;
        Sum_of_query_time = 0;
        Sum_of_response_time = 0;
        Sum_of_reconstruct_time = 0;
        Sum_of_Verify_time = 0;
    }
}
void ourTest_manytimes()
{
    for (int i = 8; i <= 20; i += 2)
    {
        for (int j = 0; j < 3; j++)
        {
            schemeTest(i, 32);
        }
        Sum_of_kgen_time = Sum_of_kgen_time / 3.0;
        Sum_of_enc_time = Sum_of_enc_time / 3.0;
        Sum_of_hash_time = Sum_of_hash_time / 3.0;
        Sum_of_query_time = Sum_of_query_time / 3.0;
        Sum_of_response_time = Sum_of_response_time / 3.0;
        Sum_of_reconstruct_time = Sum_of_reconstruct_time / 3.0;
        std::cout << " 密钥生成用时------------: " << Sum_of_kgen_time << std::endl;
        std::cout << " 加密用时------------: " << Sum_of_enc_time << std::endl;
        std::cout << " 哈希用时------------: " << Sum_of_hash_time << std::endl;
        std::cout << " OFFLINE阶段总共用时------------: " << Sum_of_kgen_time + Sum_of_enc_time + Sum_of_hash_time << std::endl;
        std::cout << " 查询用时------------: " << Sum_of_query_time << std::endl;
        std::cout << " 响应用时------------: " << Sum_of_response_time << std::endl;
        std::cout << " 重构用时------------: " << Sum_of_reconstruct_time << std::endl;
    }
}

int main()
{
    ourTest();
    return 0;
}
