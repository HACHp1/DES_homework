#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "table.cpp"


/*
���麯��,���ַ���תΪint���飨ÿ��intֻ��0��1�������������ÿ8���ַ���64λ����һ��
ע���ַ������ȱ���Ϊ8
*/
void block(int *output, const char*input){
	int i, j;
	for (j = 0; j < 8; j++){
		for (i = 0; i < 8; i++){
			//b = (b >> ��i - 1��) & 1; ȡ��iλ
			output[63 - (i + (7 - j) * 8)] = (input[j] >> i) & 1;
		}
	}
	return;
}

/*
��ԭ��������int���黹ԭΪchar����
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
IP�û�
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
IP���û�
*/

void ipr(int input[64]){
	int i;
	int temp[64];
	memcpy(temp, input, 64 * sizeof(int));
	for (i = 0; i <= 63; i++){
		input[i] = temp[IPrTable[i]];
	}
}
/*E��չ*/
void E(int*output, int input[32]){
	int i;
	for (i = 0; i <= 47; i++){
		output[i] = input[E_table[i]];
	}
}

/*
S������
*/

void S(int* output, const int* input)
{
	for (int j = 0; j < 8; j++)
	{
		int h = (input[j * 6] << 1) + input[j * 6 + 5];   //��ĺ����������
		int l = (input[j * 6 + 1] << 3) + (input[j * 6 + 2] << 2) + (input[j * 6 + 3] << 1) + input[j * 6 + 4];
		int snum = S_table[j][h][l];
		for (int i = 0; i < 4; i++)
		{
			output[j * 4 + 3 - i] = snum & 1;//��intתΪģ�����������
			snum = (snum >> 1);
		}
	}
}

/*
P�û�
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
DES feistel�ṹ�е�f����
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

/*16���ֺ���*/
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
	//��ֵ��M��ע�⽻��R��L˳��
	memcpy(M, R, 32 * sizeof(int));
	memcpy(&M[32], L, 32 * sizeof(int));
}

/*LS���ƺ���*/
void LS(int*D, int i){
	int temp[28];
	memcpy(temp, D, 28 * sizeof(int));
	int mv = LS_table[i];
	memcpy(D, &D[mv], (28 - mv)*sizeof(int));
	memcpy(&D[28 - mv], temp, mv*sizeof(int));
}

/*����Կ���ɺ���*/
void keyGen(int K[16][48], const int* originK){
	int tempK[56];
	int tempSubK[48];
	for (int i = 0; i <= 55; i++){
		tempK[i] = originK[PC1_Table[i]];//PC1�û���ȥУ��λ
	}
	int C[28];
	int D[28];
	//int tempK2[56];
	memcpy(C, tempK, 28 * sizeof(int));
	memcpy(D, &tempK[28], 28 * sizeof(int));
	for (int i = 0; i <= 15; i++){
		LS(C, i);//ѭ������
		LS(D, i);
		memcpy(tempK, C, 28 * sizeof(int));
		memcpy(&tempK[28], D, 28 * sizeof(int));
		for (int j = 0; j <= 47; j++){
			tempSubK[j] = tempK[PC2_Table[j]];//PC2�û�
		}
		memcpy(K[i], tempSubK, 48 * sizeof(int));
	}
}

/*DES����,DES����
isEnΪtrue����ܣ���֮����
*/
void DES(char*C, const char*M, char* K, bool isEn = true){
	int outputK[64] = { 0 };
	//����ʹ��block������Kת��Ϊint-0-1����
	block(outputK, K);
	//��������Կ
	int subK[16][48];
	keyGen(subK, outputK);
	//����
	int outputM[64] = { 0 };
	block(outputM, M);
	//����
	ip(outputM);
	roll(outputM, subK, isEn);
	ipr(outputM);
	//���黯Ϊ�ַ���
	C[8] = '\0';//�ӽ�������Ȼ�������
	unBlock(C, outputM);
}


void ECB(char*key, char*m, char*s, bool isEn){
	char tempchar;//�����������ʱ���������
	char tempK[9] = { 0 };//8���ַ���64λ��Ϊһ��block
	tempK[8] = '\0';
	FILE * fk = fopen(key, "r");
	for (int i = 0; i <= 7; i++){
		fscanf(fk, "%02x", &tempchar);//��ʮ�����ƶ��룬ÿ����ʮ�����ƴ洢�ַ���4λ��ת��Ϊһ�������ַ���8λ��
		tempK[i] = tempchar;
	}
	fclose(fk);

	char tempM[9] = { 0 };//8���ַ���64λ��Ϊһ��block
	tempM[8] = '\0';
	char tempC[9] = { 0 };
	tempC[8] = '\0';

	FILE * fm = fopen(m, "r");
	FILE*fs = fopen(s, "w");

	int i = 0;
	while (getc(fm) != EOF)
	{
		fseek(fm, i * 16, SEEK_SET);//ע����׼i�Ķ�λ
		for (int j = 0; j <= 7; j++){
			fscanf(fm, "%02x", &tempchar);//��ʮ�����ƶ��룬ÿ����ʮ�����ƴ洢�ַ���4λ��ת��Ϊһ�������ַ���8λ��
			tempM[j] = tempchar;
		}
		DES(tempC, tempM, tempK, isEn);
		for (int j = 0; j <= 7; j++){
			fprintf(fs, "%02X", (tempC[j] & 255));//�����ַ���ǰ�������fffff��������ȡ������Чλ
		}
		i++;
	}
	fclose(fm);
	fclose(fs);
}

void CBC(char*key, char*iv, char*m, char*s, bool isEn){
	char tempchar;//�����������ʱ���������
	char tempK[9] = { 0 };//8���ַ���64λ��Ϊһ��block
	char tempiv[9] = { 0 };

	FILE * fk = fopen(key, "r");
	FILE * fiv = fopen(iv, "r");
	for (int i = 0; i <= 7; i++){
		fscanf(fk, "%02x", &tempchar);//��ʮ�����ƶ��룬ÿ����ʮ�����ƴ洢�ַ���4λ��ת��Ϊһ�������ַ���8λ��
		tempK[i] = tempchar;
	}
	for (int i = 0; i <= 7; i++){
		fscanf(fiv, "%02x", &tempchar);
		tempiv[i] = tempchar;
	}
	fclose(fk);
	fclose(fiv);

	char tempM[9] = { 0 };//8���ַ���64λ��Ϊһ��block
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
				fprintf(fs, "%02x", (tempC[j] & 255));//�����ַ���ǰ�������fffff��������ȡ������Чλ
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

	


