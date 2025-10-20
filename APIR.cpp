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

struct APIR_Database
{
    std::vector<mpz_class> Datas;
};

struct Par_in_APIR
{
    int n;
    mpz_class p;
    pairing_t pairing;
    std::vector<std::vector<unsigned char>> h;
    element_t d;
};

APIR_Database makeDB(const std::string& fileName, int n)
{
    APIR_Database db;
    db.Datas.resize(n);
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
        size_t pos = line.find(":");
        if (pos != std::string::npos)
        {
            std::string keyPart = line.substr(0, pos);
            std::string valuePart = line.substr(pos + 1);
            mpz_class mpzvalue;
            mpzvalue.set_str(valuePart, 16);
            db.Datas[cnt] = mpzvalue;
            cnt++;
        }
    }
    if (file.bad())
    {
        std::cerr << "读取文件时出错" << std::endl;
    }
    file.close();
    return db;
}

void init_pairing(pairing_t pairing, int lambda)
{
    char param[1024];
    pbc_param_t par;
    pbc_param_init_a_gen(par, lambda, 160); // rbits = lambda, qbits =160;
    cout << "选完参数" << endl;
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

Par_in_APIR APIR_Setup(int lambda, int n)
{
    Par_in_APIR par_APIR;

    init_pairing(par_APIR.pairing, lambda);
    par_APIR.n = n;
    mpz_class p(par_APIR.pairing->r);
    par_APIR.p = p;
    par_APIR.h.resize(n);
    element_t temph;
    element_init_G1(temph, par_APIR.pairing);
    for (int i = 0; i < n; ++i)
    {
        element_random(temph);
        int ele_len = element_length_in_bytes(temph);
        par_APIR.h[i].resize(ele_len);
        element_to_bytes(par_APIR.h[i].data(), temph);
    }
    element_clear(temph);
    return par_APIR;
}

Par_in_APIR APIR_Digest(APIR_Database& db, Par_in_APIR par)
{
    element_t xj, hj, tempvalue, d;
    element_init_Zr(xj, par.pairing);
    element_init_G1(hj, par.pairing);
    element_init_G1(tempvalue, par.pairing);
    element_init_G1(d, par.pairing);
    element_set1(d);
    for (int j = 0; j < par.n; j++)
    {
        element_from_bytes(hj, par.h[j].data());
        element_set_mpz(xj, db.Datas[j].get_mpz_t());
        element_pow_zn(tempvalue, hj, xj);
        element_mul(d, d, tempvalue);
    }
    element_init_G1(par.d, par.pairing);
    element_set(par.d, d);
    element_clear(xj);
    element_clear(hj);
    element_clear(tempvalue);
    element_clear(d);
    return par;
}

struct QueryInfo
{
    element_t r;
    element_t t;
    std::vector<std::vector<unsigned char>> q;
};

QueryInfo APIR_Query(int ind, Par_in_APIR par)
{
    QueryInfo QI;
    element_init_Zr(QI.t, par.pairing);
    element_init_Zr(QI.r, par.pairing);
    element_random(QI.r);
    element_random(QI.t);
    QI.q.resize(par.n);
    element_t qj;
    element_init_G1(qj, par.pairing);
    for (int j = 0; j < par.n; j++)
    {
        if (j == ind)
        {
            element_t hj, rt;
            element_init_Zr(rt, par.pairing);
            element_add(rt, QI.r, QI.t);
            element_init_G1(hj, par.pairing);
            element_from_bytes(hj, par.h[j].data());
            element_pow_zn(qj, hj, rt);
            int ele_len = element_length_in_bytes(qj);
            QI.q[j].resize(ele_len);
            element_to_bytes(QI.q[j].data(), qj);
            element_clear(hj);
            element_clear(rt);
        }
        else
        {
            element_t hj;
            element_init_G1(hj, par.pairing);
            element_from_bytes(hj, par.h[j].data());
            element_pow_zn(qj, hj, QI.r);
            element_clear(hj);
            int ele_len = element_length_in_bytes(qj);
            QI.q[j].resize(ele_len);
            element_to_bytes(QI.q[j].data(), qj);
        }
    }
    return QI;
}

struct AnswerInfo
{
    element_t ans;
};

AnswerInfo APIR_Answer(Par_in_APIR par, APIR_Database db, QueryInfo QI)
{
    AnswerInfo AI;
    element_init_G1(AI.ans, par.pairing);
    element_set1(AI.ans);
    element_t tempvalue;
    element_init_G1(tempvalue, par.pairing);
    for (int i = 0; i < par.n; i++)
    {
        element_t q;
        element_init_G1(q, par.pairing);
        element_from_bytes(q, QI.q[i].data());
        element_pow_mpz(tempvalue, q, db.Datas[i].get_mpz_t());
        element_mul(AI.ans, AI.ans, tempvalue);
    }
    return AI;
}

void APIR_Verification(QueryInfo QI, AnswerInfo AI, Par_in_APIR par)
{
    clock_t start_verify = clock();
    element_t dr, Invdr;
    element_init_G1(dr, par.pairing);
    element_init_G1(Invdr, par.pairing);
    element_pow_zn(dr, par.d, QI.r);
    element_invert(Invdr, dr);
    element_mul(Invdr, Invdr, AI.ans);

    clock_t end_verify = clock();
    double duration_verify = (end_verify - start_verify) * 1000.0 / CLOCKS_PER_SEC;
    Sum_of_verify_time += duration_verify;
}

void APIR_SchemeTest(int dataNum, int dataSize)
{
    int lambda = 160; // Example security parameter
    std::string fileName = "DbFile_" + std::to_string(dataNum) + "_" + std::to_string(dataSize) + ".txt";
    int n = int(pow(2, dataNum));
    APIR_Database db = makeDB(fileName, n);

    clock_t start_setup = clock();
    Par_in_APIR Par_APIR = APIR_Setup(lambda, n);
    clock_t end_setup = clock();
    double duration_setup = (end_setup - start_setup) * 1000.0 / CLOCKS_PER_SEC;
    Sum_of_setup_time += duration_setup;


    clock_t start_outsource = clock();
    Par_APIR = APIR_Digest(db, Par_APIR);
    clock_t end_outsource = clock();
    double duration_outsource = (end_outsource - start_outsource) * 1000.0 / CLOCKS_PER_SEC;
    Sum_of_outsource_time += duration_outsource;

    clock_t start_query = clock();
    QueryInfo QI = APIR_Query(6, Par_APIR);
    clock_t end_query = clock();
    double duration_query = (end_query - start_query) * 1000.0 / CLOCKS_PER_SEC;
    Sum_of_query_time += duration_query;

    clock_t start_answer = clock();
    AnswerInfo AI = APIR_Answer(Par_APIR, db, QI);
    clock_t end_answer = clock();
    double duration_answer = (end_answer - start_answer) * 1000.0 / CLOCKS_PER_SEC;
    Sum_of_answer_time += duration_answer;

    APIR_Verification(QI, AI, Par_APIR);
}

int main()
{

    std::ofstream fout("APIRres.txt", std::ios::app);   // 目标文件（文件夹需已存在）
    if (!fout) return -1;
    for (int dimension = 8; dimension <= 20; dimension += 2)
    {
        std::cout << "此时维度为: " << dimension << std::endl;
        Sum_of_setup_time = 0;
        Sum_of_outsource_time = 0;
        Sum_of_query_time = 0;
        Sum_of_answer_time = 0;
        Sum_of_verify_time = 0;

        APIR_SchemeTest(dimension, 32);
        std::cout << " APIR测试完成 \n" << std::endl;
        std::cout << " APIR初始化用时: " << Sum_of_setup_time << std::endl;
        std::cout << " APIR外包用时: " << Sum_of_outsource_time << std::endl;
        std::cout << " OFFLINE TIME : " << Sum_of_setup_time + Sum_of_outsource_time << std::endl;
        std::cout << " APIR查询构造用时: " << Sum_of_query_time << std::endl;
        std::cout << " APIR响应用时: " << Sum_of_answer_time << std::endl;
        std::cout << " APIR验证用时: " << Sum_of_verify_time << std::endl;
        std::cout << " ONLINE TIME : " << Sum_of_query_time + Sum_of_answer_time + Sum_of_verify_time << std::endl;


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