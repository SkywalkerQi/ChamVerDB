#include <chrono>
#include <cmath>
#include <cstring>
#include <ctime> // For seeding random
#include <fstream>
#include <gmp.h>
#include <gmpxx.h>
#include <iostream>
#include <map>
#include <openssl/rand.h>
#include <openssl/sha.h> // For SHA256 hashing
#include <openssl/evp.h>
#include <pbc/pbc.h>
#include <random>
#include <regex>
#include <stdexcept>
#include <stdio.h>
#include <string.h>
#include <string>
#include <unistd.h>
#include <vector>
using namespace std;

// double Sum_of_enc_time = 0;
double Sum_of_setup_time = 0;
double Sum_of_outsource_time = 0;
double Sum_of_query_time = 0;
double Sum_of_answer_time = 0;
double Sum_of_verify_time = 0;

struct Par_in_VUSDB
{
    int l;
    int n;
    mpz_class p;
    pairing_t pairing;
    element_t g;
    std::vector<std::vector<unsigned char>> A1;
    std::vector<std::vector<std::vector<unsigned char>>> A2;
};

struct UserKeyPair
{
    std::pair<mpz_class, mpz_class> sk;
    element_t pk;
};
struct Bucket
{
    std::vector<std::vector<unsigned char>> Datas;
};

struct VUSDB_Database
{
    std::vector<Bucket> Buckets;
    int bucketNum;
    int bucketCap;
};

struct ClientData
{
    element_t I;
    VUSDB_Database prepared_db;
    element_t C;
    element_t h;
    element_t phi;
};


Bucket InitializeBucket(Par_in_VUSDB par)
{
    Bucket bucket;
    bucket.Datas.resize(par.l);
    return bucket;
}

VUSDB_Database InitializeDatabase(Par_in_VUSDB par)
{
    VUSDB_Database db;
    db.Buckets.resize(par.l);
    db.bucketNum = par.l;
    db.bucketCap = par.l;

    for (int i = 0; i < db.bucketNum; ++i)
    {
        db.Buckets[i] = InitializeBucket(par);
    }
    return db;
}

VUSDB_Database newMakeDB(Par_in_VUSDB VUSDB_par)
{
    VUSDB_Database db = InitializeDatabase(VUSDB_par);
    return db;
}

// 输出参数
void PrintVUSDBPar(Par_in_VUSDB Par)
{
    element_t e_print;
    element_init_G1(e_print, Par.pairing);
    for (int i = 0; i < Par.l; i++)
    {
        element_from_bytes(e_print, Par.A1[i].data());
    }
    for (int i = 0; i < Par.l; i++)
    {
        for (int j = 0; j < Par.l; j++)
        {
            if (i == j)
                continue;
            element_from_bytes(e_print, Par.A2[i][j].data());
        }
    }
    element_clear(e_print);
}

void H(element_t ele_h, const std::string& input, Par_in_VUSDB par)
{
    unsigned char hash[SHA256_DIGEST_LENGTH];
    SHA256(reinterpret_cast<const unsigned char*>(input.c_str()), input.size(), hash);
    mpz_class res;
    mpz_import(res.get_mpz_t(), SHA256_DIGEST_LENGTH, 1, sizeof(hash[0]), 0, 0, hash);
    res %= par.p;
    element_set_mpz(ele_h, res.get_mpz_t());
}

void F(element_t ele_h, mpz_class key, std::string input_str, Par_in_VUSDB par)
{
    std::string key_str = key.get_str(10); 
    std::string combined = key_str + input_str;
    H(ele_h, combined, par);
}

void init_pairing(pairing_t pairing, int lambda)
{
    char param[1024];
    pbc_param_t par;
    pbc_param_init_a_gen(par, lambda, 160); 
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

mpz_class gen_random_mpz(mpz_class p)
{
    if (p <= 0)
        throw std::invalid_argument("p must be > 0");
    size_t bits = mpz_sizeinbase(p.get_mpz_t(), 2); 
    if (bits == 0)
        bits = 1;
    size_t bytes = (bits + 7) / 8;

    std::ifstream urandom("/dev/urandom", std::ios::binary);
    if (!urandom.is_open())
        throw std::runtime_error("failed to open /dev/urandom");

    mpz_class mask = (mpz_class(1) << bits) - 1; 
    mpz_class r;

    while (true)
    {
        std::vector<unsigned char> buf(bytes);
        urandom.read(reinterpret_cast<char*>(buf.data()), bytes);
        if (static_cast<size_t>(urandom.gcount()) != bytes)
            throw std::runtime_error("failed to read enough bytes from /dev/urandom");
        mpz_import(r.get_mpz_t(), bytes, 1, 1, 0, 0, buf.data());
        r &= mask;
        if (r < p)
        {
            return r; 
        }
    }
}

// KeyGen function
Par_in_VUSDB KeyGen(int lambda, int l, int n)
{
    std::cout << " ————————————————————————执行KeyGen函数.. " << std::endl;
    Par_in_VUSDB par_VUSDB;
    // Pairing
    init_pairing(par_VUSDB.pairing, lambda);
    par_VUSDB.l = l;
    par_VUSDB.n = n;
    // Get the prime order p(Z_p)
    mpz_class p(par_VUSDB.pairing->r);
    par_VUSDB.p = p;
    // Choose random generator g in G
    element_init_G1(par_VUSDB.g, par_VUSDB.pairing);
    element_random(par_VUSDB.g); // Random element in G1; since order p is prime, likely a generator
    std::vector<mpz_class> a;
    for (int i = 0; i < l; ++i)
    {
        a.push_back(gen_random_mpz(p));
    }
    par_VUSDB.A1.resize(l);
    for (int i = 0; i < l; ++i)
    {
        element_t tempAi;
        element_init_G1(tempAi, par_VUSDB.pairing);
        element_pow_mpz(tempAi, par_VUSDB.g, a[i].get_mpz_t());
        int ele_len = element_length_in_bytes(tempAi);
        par_VUSDB.A1[i].resize(ele_len);
        element_to_bytes(par_VUSDB.A1[i].data(), tempAi);
        element_clear(tempAi);
    }
    par_VUSDB.A2.resize(l, std::vector<std::vector<unsigned char>>(l));
    for (int i = 0; i < l; ++i)
    {
        for (int j = 0; j < l; ++j)
        {
            if (i == j)
                continue; // Skip i==j as per algorithm
            element_t tempAij;
            element_init_G1(tempAij, par_VUSDB.pairing);
            mpz_class exp = (a[i] * a[j]) % p;
            element_pow_mpz(tempAij, par_VUSDB.g, exp.get_mpz_t());
            int ele_len = element_length_in_bytes(tempAij);
            par_VUSDB.A2[i][j].resize(ele_len);
            element_to_bytes(par_VUSDB.A2[i][j].data(), tempAij);
            element_clear(tempAij);
        }
    }
    return par_VUSDB;
}

UserKeyPair UKeyGen(Par_in_VUSDB par)
{
    UserKeyPair ukp;
    ukp.sk.first = gen_random_mpz(par.p);
    ukp.sk.second = gen_random_mpz(par.p);
    element_init_G1(ukp.pk, par.pairing);
    element_pow_mpz(ukp.pk, par.g, ukp.sk.second.get_mpz_t());
    return ukp;
}

void KVWrite(int dataNum, int dataSize) // 写入的文件中, 数据量为2^dataNum, 数据大小为 dataSize-bit
{
    std::string fileName = "DbFile_" + std::to_string(dataNum) + "_" + std::to_string(dataSize) + ".txt";
    std::ofstream file(fileName);
    if (!file.is_open())
    {
        std::cerr << "无法创建文件: " << fileName << std::endl;
        return;
    }
    // randgen
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

// 工具: 实现类element_from_hash功能
void element_from_hash_Zr(element_t e, const void* data, int len, Par_in_VUSDB par)
{
    unsigned char digest[SHA256_DIGEST_LENGTH];
    SHA256(static_cast<const unsigned char*>(data), len, digest);
    mpz_class r;
    ::mpz_import(r.get_mpz_t(), sizeof(digest), 1, 1, 0, 0, digest);
    r %= par.p; 
    element_set_mpz(e, r.get_mpz_t());
}

void print_hex(const char* title, const std::vector<unsigned char>& buf)
{
    std::cout << title << " (" << buf.size() << " bytes)\n";
    for (unsigned char c : buf)
        printf("%02x", c);
    std::cout << "\n";
}

std::vector<unsigned char> aes_encrypt(const std::vector<unsigned char>& key,
    const std::vector<unsigned char>& iv,
    const std::vector<unsigned char>& plain)
{
    EVP_CIPHER_CTX* ctx = EVP_CIPHER_CTX_new();
    std::vector<unsigned char> cipher(plain.size() + EVP_MAX_BLOCK_LENGTH);
    int len = 0, total = 0;

    EVP_EncryptInit_ex(ctx, EVP_aes_256_cbc(), nullptr, key.data(), iv.data());
    EVP_EncryptUpdate(ctx, cipher.data(), &len, plain.data(), plain.size());
    total += len;
    EVP_EncryptFinal_ex(ctx, cipher.data() + total, &len);
    total += len;
    cipher.resize(total);
    EVP_CIPHER_CTX_free(ctx);
    return cipher;
}

std::vector<unsigned char> aes_decrypt(const std::vector<unsigned char>& key,
    const std::vector<unsigned char>& iv,
    const std::vector<unsigned char>& cipher)
{
    EVP_CIPHER_CTX* ctx = EVP_CIPHER_CTX_new();
    std::vector<unsigned char> plain(cipher.size() + EVP_MAX_BLOCK_LENGTH);
    int len = 0, total = 0;

    EVP_DecryptInit_ex(ctx, EVP_aes_256_cbc(), nullptr, key.data(), iv.data());
    EVP_DecryptUpdate(ctx, plain.data(), &len, cipher.data(), cipher.size());
    total += len;
    EVP_DecryptFinal_ex(ctx, plain.data() + total, &len);
    total += len;
    plain.resize(total);
    EVP_CIPHER_CTX_free(ctx);
    return plain;
}

const size_t AES_KEY_LEN = 32; // 256 bit
const size_t AES_IV_LEN = 16;  // 128 bit
std::vector<unsigned char> key(AES_KEY_LEN);
std::vector<unsigned char> iv(AES_IV_LEN);

// 加密数据，简单实用对称密码算法进行加密
std::vector<unsigned char> VUSDB_dataEnc(string m)
{
    std::vector<unsigned char> plaintext(m.begin(), m.end());
    auto ciphertext = aes_encrypt(key, iv, plaintext);
    return ciphertext;
}

// 解密数据，简单实用对称密码算法进行加密
std::vector<unsigned char> VUSDB_dataDec(std::vector<unsigned char> ciphertext)
{
    auto decrypted = aes_decrypt(key, iv, ciphertext);
    return decrypted;
}

// 加密数据，简单实用对称密码算法进行加密
ClientData VUSDB_Outsource(UserKeyPair ukp, const std::string& fileName, VUSDB_Database& db, Par_in_VUSDB par)
{
    std::ifstream file(fileName);
    if (!file.is_open())
    {
        std::cerr << "文件 " << fileName << " 不存在, 请先创建文件..." << std::endl;
    }
    int cnt = 0;
    std::string line;
    std::regex number_regex("\\d+");

    while (std::getline(file, line))
    {
        // std::cout << "读取的数据为: " << line << std::endl;
        size_t pos = line.find(":");
        if (pos != std::string::npos)
        {
            std::string keyPart = line.substr(0, pos);
            std::string valuePart = line.substr(pos + 1);
            db.Buckets[cnt / par.l].Datas[cnt % par.l] = VUSDB_dataEnc(valuePart);
            cnt++;
        }
    }
    if (file.bad())
    {
        std::cerr << "读取文件时出错" << std::endl;
    }
    int row = db.bucketNum;
    int column = db.bucketCap;

    element_t OutProdSum, sumF, sumProdhi;
    element_init_G1(OutProdSum, par.pairing);
    element_set1(OutProdSum);
    element_init_Zr(sumF, par.pairing);
    element_set0(sumF);
    element_init_G1(sumProdhi, par.pairing);
    element_set1(sumProdhi);

    element_t I;
    element_init_Zr(I, par.pairing);
    element_random(I);

    for (int i = 0; i < row; ++i)
    {
        element_t sumTime;
        element_init_G1(sumTime, par.pairing);
        element_set1(sumTime);
        for (int j = 0; j < column; ++j)
        {
            element_t A, v, tempres;
            element_init_Zr(v, par.pairing);
            element_init_G1(A, par.pairing);
            element_init_G1(tempres, par.pairing);
            element_from_bytes(A, par.A1[j].data());

            element_from_hash_Zr(v, db.Buckets[i].Datas[j].data(), db.Buckets[i].Datas[j].size(), par);

            element_pow_zn(tempres, A, v);
            element_mul(sumTime, sumTime, tempres);

            element_clear(A);
            element_clear(v);
            element_clear(tempres);
        }

        element_t _F, randkey;
        element_init_Zr(_F, par.pairing);

        element_init_Zr(randkey, par.pairing);

        element_random(randkey);
        mpz_class mpz_I, mpz_randkey;
        element_to_mpz(mpz_I.get_mpz_t(), I);
        element_to_mpz(mpz_randkey.get_mpz_t(), I);

        F(_F, mpz_randkey, mpz_I.get_str(10) + std::to_string(i), par); 
        element_t gF;
        element_init_G1(gF, par.pairing);
        element_pow_zn(gF, par.g, _F);

        element_add(sumF, sumF, _F);

        element_t _H;
        element_init_Zr(_H, par.pairing);
        H(_H, mpz_I.get_str(10) + std::to_string(i), par);

        element_t tempvalue1;
        element_init_G1(tempvalue1, par.pairing);
        element_pow_zn(tempvalue1, sumTime, _H);
        element_mul(tempvalue1, gF, tempvalue1);
        
        element_mul(OutProdSum, OutProdSum, tempvalue1);

        element_clear(sumTime);
        element_clear(_F);
        element_clear(randkey);
        element_clear(gF);
        element_clear(_H);
        element_clear(tempvalue1);
    }

    element_pow_mpz(OutProdSum, OutProdSum, ukp.sk.second.get_mpz_t());
    ClientData transData;
    element_init_G1(transData.I, par.pairing);
    element_init_G1(transData.C, par.pairing);
    element_init_G1(transData.h, par.pairing);
    element_init_Zr(transData.phi, par.pairing);
    element_set(transData.I, I);
    transData.prepared_db = db;
    element_set(transData.C, OutProdSum);
    element_set(transData.h, sumProdhi);
    element_set(transData.phi, sumF);
    element_clear(OutProdSum);
    element_clear(sumF);
    element_clear(sumProdhi);
    element_clear(I);
    file.close();
    return transData;
}

struct QueryInfo
{
    int db_index;
    int data_index;
    element_t Gama1;
    element_t Gama2;
    element_t Gama3;
    element_t Gama4;
    element_t Gama5;
};
struct AnswerInfo
{
    element_t I;
    element_t v;
    element_t beta;
    element_t d;
    element_t Gama1;
    element_t Gama2;
    element_t Gama3;
    element_t Gama4;
    element_t Gama5;
    element_t C;
};

QueryInfo VUSDB_QueryGen(int x, UserKeyPair ukp, ClientData transData, Par_in_VUSDB par)
{
    QueryInfo QI;
    int i0, j0;
    i0 = x / (par.l);
    j0 = x - (i0 * par.l);
    QI.data_index = x;
    QI.db_index = 0;
    element_t r;
    element_init_Zr(r, par.pairing);
    element_random(r);
    element_init_G1(QI.Gama1, par.pairing);
    element_init_G1(QI.Gama2, par.pairing);
    element_init_G1(QI.Gama3, par.pairing);
    element_init_G1(QI.Gama4, par.pairing);
    element_init_G1(QI.Gama5, par.pairing);

    element_pow_zn(QI.Gama1, par.g, r); // 计算Gama1

    element_pow_zn(QI.Gama2, ukp.pk, r); // 计算Gama2

    element_t Aj;
    element_init_G1(Aj, par.pairing);
    element_from_bytes(Aj, par.A1[j0].data());
    element_pow_zn(QI.Gama3, Aj, r); // 计算Gama3

    element_t r_gama_theta;
    element_init_Zr(r_gama_theta, par.pairing);
    element_mul_mpz(r_gama_theta, r, ukp.sk.second.get_mpz_t());
    element_pow_zn(QI.Gama4, Aj, r_gama_theta);     // 计算Gama4
    element_pow_zn(QI.Gama5, par.g, transData.phi); // 计算Gama5

    element_clear(r);
    element_clear(Aj);
    element_clear(r_gama_theta);
    return QI;
}

AnswerInfo VUSDB_QueryAnswer(VUSDB_Database& db, QueryInfo QI, ClientData transData, Par_in_VUSDB par)
{
    int i0, j0;
    i0 = QI.data_index / (par.l);
    j0 = QI.data_index - (i0 * par.l);

    AnswerInfo AI;
    element_init_same_as(AI.I, transData.I);
    element_init_Zr(AI.v, par.pairing);
    element_init_same_as(AI.Gama1, QI.Gama1);
    element_init_same_as(AI.Gama2, QI.Gama2);
    element_init_same_as(AI.Gama3, QI.Gama3);
    element_init_same_as(AI.Gama4, QI.Gama4);
    element_init_same_as(AI.Gama5, QI.Gama5);
    element_init_same_as(AI.C, transData.C);
    element_set(AI.I, transData.I);
    element_set(AI.Gama1, QI.Gama1);
    element_set(AI.Gama2, QI.Gama2);
    element_set(AI.Gama3, QI.Gama3);
    element_set(AI.Gama4, QI.Gama4);
    element_set(AI.Gama5, QI.Gama5);
    element_set(AI.C, transData.C);
    element_from_hash_Zr(AI.v, db.Buckets[i0].Datas[j0].data(), db.Buckets[i0].Datas[j0].size(), par);
    mpz_class mpz_I;
    element_to_mpz(mpz_I.get_mpz_t(), transData.I);
    element_init_Zr(AI.beta, par.pairing);
    element_set0(AI.beta);
    element_init_G1(AI.d, par.pairing);
    element_set1(AI.d);

    for (int i = 0; i < par.l; i++)
    {
        element_t _H, tempv;
        element_init_Zr(_H, par.pairing);
        element_init_Zr(tempv, par.pairing);
        H(_H, mpz_I.get_str(10) + std::to_string(i0), par);
        element_from_hash_Zr(tempv, db.Buckets[i].Datas[j0].data(), db.Buckets[i].Datas[j0].size(), par);
        element_mul(_H, _H, tempv);
        element_add(AI.beta, AI.beta, _H);
        element_t tempd;
        element_init_G1(tempd, par.pairing);
        element_set1(tempd);

        element_t A, tempvv, tempres;
        element_init_G1(A, par.pairing);
        element_init_G1(tempres, par.pairing);
        element_init_Zr(tempvv, par.pairing);

        for (int j = 0; j < par.l; ++j)
        {
            if (j == j0)
                continue;
            element_from_bytes(A, par.A2[j0][j].data());
            element_from_hash_Zr(tempvv, db.Buckets[i].Datas[j].data(), db.Buckets[i].Datas[j].size(), par);
            element_pow_zn(tempres, A, tempvv);
            element_mul(tempd, tempd, tempres);
        }

        element_pow_zn(tempd, tempd, _H);
        element_mul(AI.d, AI.d, tempd);

        element_clear(A);
        element_clear(tempvv);
        element_clear(tempres);

        element_clear(tempd);
        element_clear(_H);
        element_clear(tempv);
    }
    return AI;
}

void VUSDB_Verification(int x, AnswerInfo AI, UserKeyPair ukp, Par_in_VUSDB par)
{
    clock_t start_verify = clock();
    int i0, j0;
    i0 = x / par.l;
    j0 = x % (par.l);
    element_t _H;
    element_init_Zr(_H, par.pairing);
    mpz_class mpz_I;
    element_to_mpz(mpz_I.get_mpz_t(), AI.I);
    H(_H, mpz_I.get_str(10) + std::to_string(i0), par);

    element_t powervalue;
    element_init_Zr(powervalue, par.pairing);
    element_mul(powervalue, _H, AI.v);
    element_add(powervalue, powervalue, AI.beta);

    element_t newGama4;
    element_init_G1(newGama4, par.pairing);
    element_pow_zn(newGama4, AI.Gama4, powervalue);

    element_t E1Left, E1Right, E2Left, E2Right, E3Left, E3Right, E4Left, E4Right, E4Right1, E4Right2, E4Right3;
    element_init_GT(E1Left, par.pairing);
    element_init_GT(E1Right, par.pairing);
    element_init_GT(E2Left, par.pairing);
    element_init_GT(E2Right, par.pairing);
    element_init_GT(E3Left, par.pairing);
    element_init_GT(E3Right, par.pairing);
    element_init_GT(E4Left, par.pairing);
    element_init_GT(E4Right1, par.pairing);
    element_init_GT(E4Right2, par.pairing);
    element_init_GT(E4Right3, par.pairing);

    pairing_apply(E1Left, AI.Gama1, ukp.pk, par.pairing);
    pairing_apply(E1Right, AI.Gama2, par.g, par.pairing);
    element_cmp(E1Left, E1Right)
    element_t Aj0;
    element_init_G1(Aj0, par.pairing);
    element_from_bytes(Aj0, par.A1[j0].data());
    pairing_apply(E2Left, AI.Gama1, Aj0, par.pairing);
    pairing_apply(E2Right, AI.Gama3, par.g, par.pairing);
    element_cmp(E2Left, E2Right))
    pairing_apply(E3Left, AI.Gama2, Aj0, par.pairing);
    pairing_apply(E3Right, AI.Gama4, par.g, par.pairing);
    element_cmp(E3Left, E3Right)
    pairing_apply(E4Left, AI.C, AI.Gama3, par.pairing);
    pairing_apply(E4Right1, newGama4, Aj0, par.pairing);
    pairing_apply(E4Right2, AI.Gama4, AI.Gama5, par.pairing);
    pairing_apply(E4Right3, AI.d, AI.Gama2, par.pairing);
    element_init_same_as(E4Right, E4Right1);
    element_mul(E4Right, E4Right1, E4Right2);
    element_mul(E4Right, E4Right, E4Right3);
    element_cmp(E4Left, E4Right)
    element_clear(_H);
    element_clear(powervalue);
    element_clear(newGama4);
    element_clear(E1Left);
    element_clear(E1Right);
    element_clear(E2Left);
    element_clear(E2Right);
    element_clear(E3Left);
    element_clear(E3Right);
    element_clear(E4Left);
    element_clear(E4Right);
    element_clear(Aj0);

    clock_t end_verify = clock();
    double duration_verify = (end_verify - start_verify) * 1000.0 / CLOCKS_PER_SEC;
    Sum_of_verify_time += duration_verify;
}

void VUSDB_SchemeTest(int dataNum, int dataSize)
{
    int lambda = 160;                 
    int l = int(pow(2, dataNum / 2)); // l 代表行数, 假设dataNum为x, 则l应该为sqrt(2^x), 即2^(x/2)
    int n = 10;                       

    clock_t start_setup = clock();
    Par_in_VUSDB Par_VUSDB = KeyGen(lambda, l, n);
    UserKeyPair ukp = UKeyGen(Par_VUSDB);
    clock_t end_setup = clock();
    double duration_setup = (end_setup - start_setup) * 1000.0 / CLOCKS_PER_SEC;
    Sum_of_setup_time += duration_setup;
    VUSDB_Database db = newMakeDB(Par_VUSDB);
    std::string fileName = "DbFile_" + std::to_string(dataNum) + "_" + std::to_string(dataSize) + ".txt";
    
    clock_t start_outsource = clock();
    ClientData ct = VUSDB_Outsource(ukp, fileName, db, Par_VUSDB);
    clock_t end_outsource = clock();
    double duration_outsource = (end_outsource - start_outsource) * 1000.0 / CLOCKS_PER_SEC;
    Sum_of_outsource_time += duration_outsource;

    clock_t start_query = clock();
    QueryInfo QI = VUSDB_QueryGen(6, ukp, ct, Par_VUSDB);
    clock_t end_query = clock();
    double duration_query = (end_query - start_query) * 1000.0 / CLOCKS_PER_SEC;
    Sum_of_query_time += duration_query;

    clock_t start_answer = clock();
    AnswerInfo AI = VUSDB_QueryAnswer(db, QI, ct, Par_VUSDB);
    clock_t end_answer = clock();
    double duration_answer = (end_answer - start_answer) * 1000.0 / CLOCKS_PER_SEC;
    Sum_of_answer_time += duration_answer;
    VUSDB_Verification(6, AI, ukp, Par_VUSDB);
}

int main()
{
    std::ofstream fout("test2res.txt", std::ios::app);   // 目标文件（文件夹需已存在）
    if (!fout) return -1;
    for (int dimension = 8; dimension <= 18; dimension += 2)
    {
        std::cout << "此时维度为: " << dimension << std::endl;
        Sum_of_setup_time = 0;
        Sum_of_outsource_time = 0;
        Sum_of_query_time = 0;
        Sum_of_answer_time = 0;
        Sum_of_verify_time = 0;
        VUSDB_SchemeTest(dimension, 32);
        std::cout << " 测试完成 ------------------------ " << dimension << std::endl;
        std::cout << " 初始化用时: " << Sum_of_setup_time << " ms " << std::endl;
        std::cout << " 加密用时: " << Sum_of_outsource_time << " ms " << std::endl;
        std::cout << " 查询构造用时: " << Sum_of_query_time << " ms " << std::endl;
        std::cout << " 查询响应用时: " << Sum_of_answer_time << " ms " << std::endl;
        std::cout << " 验证用时: " << Sum_of_verify_time << " ms " << std::endl;
        std::cout << " ******************************************************* " << std::endl;
        fout << " 测试完成 ------------------------ " << dimension << '\n'
            << " 初始化用时: " << Sum_of_setup_time << '\n'
            << " 加密用时: " << Sum_of_outsource_time << '\n'
            << " 查询构造用时: " << Sum_of_query_time << '\n'
            << " 查询响应用时: " << Sum_of_answer_time << '\n'
            << " 验证用时: " << Sum_of_verify_time << '\n'
            << " ******************************************************* " << '\n';
        cout << " 写入完成 " << endl;
    }
    return 0;
}

