#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "table.cpp"


/*
分组函数,将字符串转为int数组（每个int只记0或1，方便操作），每8个字符（64位）分一块
注：字符串长度必须为8
*/
void block(int *output, const char*input){
	int i, j;
	for (j = 0; j < 8; j++){
		for (i = 0; i < 8; i++){
			//b = (b >> （i - 1）) & 1; 取第i位
			output[63 - (i + (7 - j) * 8)] = (input[j] >> i) & 1;
		}
	}
	return;
}

/*
还原函数，将int数组还原为char数组
*/

void unBlock(char*output, int*input){
	int i = 0, j = 0;
	int slen = strlen(output);
	for (j; j < 8; j++){
		output[j] = '\0';
		for (i; i < 8; i++){
			output[j] += input[i + j * 8] << (7 - i);
		}
		i = 0;
	}
}

/*
IP置换
*/

void ip(int input[64]){
	int i;
	int temp[64];
	memcpy(temp, input, 64 * sizeof(int));
	for (i = 0; i <= 63; i++){
		input[i] = temp[IPTable[i]];
	}
}
/*
IP逆置换
*/

void ipr(int input[64]){
	int i;
	int temp[64];
	memcpy(temp, input, 64 * sizeof(int));
	for (i = 0; i <= 63; i++){
		input[i] = temp[IPrTable[i]];
	}
}
/*E拓展*/
void E(int*output, int input[32]){
	int i;
	for (i = 0; i <= 47; i++){
		output[i] = input[E_table[i]];
	}
}

/*
S盒运算
*/

void S(int* output, const int* input)
{
	for (int j = 0; j < 8; j++)
	{
		int h = (input[j * 6] << 1) + input[j * 6 + 5];   //表的横纵坐标计算
		int l = (input[j * 6 + 1] << 3) + (input[j * 6 + 2] << 2) + (input[j * 6 + 3] << 1) + input[j * 6 + 4];
		int snum = S_table[j][h][l];
		for (int i = 0; i < 4; i++)
		{
			output[j * 4 + 3 - i] = snum & 1;//将int转为模拟二进制数组
			snum = (snum >> 1);
		}
	}
}

/*
P置换
*/
void P(int*input){
	int i;
	int temp[32];
	memcpy(temp, input, 32 * sizeof(int));
	for (i = 0; i <= 31; i++){
		input[i] = temp[P_table[i]];
	}
}
/*
DES feistel结构中的f函数
*/

void f(int* R, const int K[48]){
	int temp[48];
	E(temp, R);
	for (int i = 0; i <= 47; i++){
		temp[i] = temp[i] ^ K[i];
	}
	S(R, temp);
	P(R);
}

/*16次轮函数*/
void roll(int*M, const int(*K)[48], bool isEn){
	int L[32];
	int R[32];
	int TempR[32];
	memcpy(L, M, 32 * sizeof(int));
	memcpy(R, &M[32], 32 * sizeof(int));
	for (int j = 0; j <= 15; j++){
		memcpy(TempR, R, 32 * sizeof(int));
		if (isEn){
			f(R, K[j]);
		}
		else
		{
			f(R, K[15 - j]);
		}
		for (int i = 0; i <= 31; i++){
			R[i] = R[i] ^ L[i];
		}
		memcpy(L, TempR, 32 * sizeof(int));
	}
	//赋值给M，注意交换R、L顺序
	memcpy(M, R, 32 * sizeof(int));
	memcpy(&M[32], L, 32 * sizeof(int));
}

/*LS左移函数*/
void LS(int*D, int i){
	int temp[28];
	memcpy(temp, D, 28 * sizeof(int));
	int mv = LS_table[i];
	memcpy(D, &D[mv], (28 - mv)*sizeof(int));
	memcpy(&D[28 - mv], temp, mv*sizeof(int));
}

/*子密钥生成函数*/
void keyGen(int K[16][48], const int* originK){
	int tempK[56];
	int tempSubK[48];
	for (int i = 0; i <= 55; i++){
		tempK[i] = originK[PC1_Table[i]];//PC1置换，去校验位
	}
	int C[28];
	int D[28];
	//int tempK2[56];
	memcpy(C, tempK, 28 * sizeof(int));
	memcpy(D, &tempK[28], 28 * sizeof(int));
	for (int i = 0; i <= 15; i++){
		LS(C, i);//循环左移
		LS(D, i);
		memcpy(tempK, C, 28 * sizeof(int));
		memcpy(&tempK[28], D, 28 * sizeof(int));
		for (int j = 0; j <= 47; j++){
			tempSubK[j] = tempK[PC2_Table[j]];//PC2置换
		}
		memcpy(K[i], tempSubK, 48 * sizeof(int));
	}
}

/*DES加密,DES解密
isEn为true则加密，反之解密
*/
void DES(char*C, const char*M, char* K, bool isEn = true){
	int outputK[64] = { 0 };
	//这里使用block函数将K转化为int-0-1数组
	block(outputK, K);
	//生成子密钥
	int subK[16][48];
	keyGen(subK, outputK);
	//分组
	int outputM[64] = { 0 };
	block(outputM, M);
	//加密
	ip(outputM);
	roll(outputM, subK, isEn);
	ipr(outputM);
	//将组化为字符串
	C[8] = '\0';//加结束符不然会出问题
	unBlock(C, outputM);
}


void ECB(char*key, char*m, char*s, bool isEn){
	char tempchar;//用来解决读入时溢出的问题
	char tempK[9] = { 0 };//8个字符（64位）为一个block
	tempK[8] = '\0';
	FILE * fk = fopen(key, "r");
	for (int i = 0; i <= 7; i++){
		fscanf(fk, "%02x", &tempchar);//以十六进制读入，每两个十六进制存储字符（4位）转化为一个变量字符（8位）
		tempK[i] = tempchar;
	}
	fclose(fk);

	char tempM[9] = { 0 };//8个字符（64位）为一个block
	tempM[8] = '\0';
	char tempC[9] = { 0 };
	tempC[8] = '\0';

	FILE * fm = fopen(m, "r");
	FILE*fs = fopen(s, "w");

	int i = 0;
	while (getc(fm) != EOF)
	{
		fseek(fm, i * 16, SEEK_SET);//注意找准i的定位
		for (int j = 0; j <= 7; j++){
			fscanf(fm, "%02x", &tempchar);//以十六进制读入，每两个十六进制存储字符（4位）转化为一个变量字符（8位）
			tempM[j] = tempchar;
		}
		DES(tempC, tempM, tempK, isEn);
		for (int j = 0; j <= 7; j++){
			fprintf(fs, "%02X", (tempC[j] & 255));//由于字符串前被填充了fffff，在这里取后面有效位
		}
		i++;
	}
	fclose(fm);
	fclose(fs);
}

void CBC(char*key, char*iv, char*m, char*s, bool isEn){
	char tempchar;//用来解决读入时溢出的问题
	char tempK[9] = { 0 };//8个字符（64位）为一个block
	char tempiv[9] = { 0 };

	FILE * fk = fopen(key, "r");
	FILE * fiv = fopen(iv, "r");
	for (int i = 0; i <= 7; i++){
		fscanf(fk, "%02x", &tempchar);//以十六进制读入，每两个十六进制存储字符（4位）转化为一个变量字符（8位）
		tempK[i] = tempchar;
	}
	for (int i = 0; i <= 7; i++){
		fscanf(fiv, "%02x", &tempchar);
		tempiv[i] = tempchar;
	}
	fclose(fk);
	fclose(fiv);

	char tempM[9] = { 0 };//8个字符（64位）为一个block
	tempM[8] = '\0';
	char tempC[9] = { 0 };
	for (int i = 0; i <= 7; i++){
		tempC[i] = tempiv[i];//C0=IV
	}

	FILE * fm = fopen(m, "r");
	FILE*fs = fopen(s, "w");

	int i = 0;
	if (isEn){
		while (getc(fm) != EOF)
		{
			fseek(fm, i * 16, SEEK_SET);
			for (int j = 0; j <= 7; j++){
				fscanf(fm, "%02x", &tempchar);
				tempM[j] = tempchar;
			}

			for (int j = 0; j <= 7; j++){
				tempM[j] = tempM[j] ^ tempC[j];
			}

			DES(tempC, tempM, tempK);//CI=E(M^CI-1)
			for (int j = 0; j <= 7; j++){
				fprintf(fs, "%02x", (tempC[j] & 255));//由于字符串前被填充了fffff，在这里取后面有效位
			}
			i++;
		}
	}
	else{
		while (getc(fm) != EOF)
		{
			fseek(fm, i * 16, SEEK_SET);
			for (int j = 0; j <= 7; j++){
				fscanf(fm, "%2x", &tempchar);
				tempM[j] = tempchar;
			}
			DES(tempC, tempM, tempK, 0);
			for (int j = 0; j <= 7; j++){
				tempC[j] = tempC[j] ^ tempiv[j];
			}
			for (int i = 0; i <= 7; i++){
				tempiv[i] = tempM[i];
			}
			for (int j = 0; j <= 7; j++){
				fprintf(fs, "%02X", (tempC[j] & 255));
			}
			i++;
		}
	}
	fclose(fm);
	fclose(fs);
}
int main()
{
	printf(
		"******************************************************\n"
		"******************************************************\n"
		"******************************************************\n"
		"************CHP's DES encrypter v1.0!*****************\n"
		"******************************************************\n"
		"******************************************************\n"
		"******************************************************\n"
		"\n"
		);
	char flag;
	while (1){
		printf("Models and selections:\n0 : ECB \n1 : CBC\n2 : exit \n");
		printf("input:");
		flag = getchar();
		fflush(stdin);
		if (flag == '0') {
			ECB("des_key.txt", "des_messages.txt", "des_secret.txt", 1);
			ECB("des_key.txt", "des_secret.txt", "des_decrypted.txt", 0);
		}
		else if (flag == '1'){
			CBC("des_key.txt", "des_iv.txt", "des_messages.txt", "des_secret.txt", 1);
			CBC("des_key.txt", "des_iv.txt", "des_secret.txt", "des_decrypted.txt", 0);
		}
		else if (flag == '2'){
			break;
		}
		else{
			printf("Number is wrong,please input again:\n");
		}
	}
	return 0;
}

	


