// Software: LZW
// Language: Java
// Author: Hy Truong Son
// Major: BSc. Computer Science
// Class: 2013 - 2016
// Institution: Eotvos Lorand University
// Email: sonpascal93@gmail.com
// Website: http://people.inf.elte.hu/hytruongson/
// Copyright 2015 (c) Hy Truong Son. All rights reserved.

import java.io.*;

public class LZWOldVersion {
	
	static int MaxN = 200000;
	
	static int ByteValue = 256;
	static int nBitsByte = 8;
	static int LengthLimit = 14;
	
	static int nWords, Length;
	
	static class SearchTrie {
		public int IsWord;
		public int LeftChild, RightChild;
	}
	static int nST;
	static SearchTrie ST[] = new SearchTrie [MaxN];
	
	static int top, SumByte;
	static int stack[] = new int [MaxN];
	static int First[] = new int [MaxN];
	static int Second[] = new int [MaxN];
	
	static int Dictionary[][] = new int [1 << LengthLimit][];
	
	public static void AddSearchTrie(int IsWord, int LeftChild, int RightChild){
		ST[nST] = new SearchTrie();
		ST[nST].IsWord = IsWord;
		ST[nST].LeftChild = LeftChild;
		ST[nST].RightChild = RightChild;
		nST++;
	}
	
	public static void Init(){
		int i, j, root, bit, aByte;
		
		nWords = ByteValue;
		Length = nBitsByte;
		
		top = 0;
		SumByte = 0;
		nST = 0;
		AddSearchTrie(-1, -1, -1);
		
		for (i = 0; i < ByteValue; i++){
			root = 0;
			aByte = i;
			
			for (j = 0; j < Length; j++){
				bit = aByte % 2;
				
				if (bit == 0){
					if (ST[root].LeftChild == -1){
						AddSearchTrie(-1, -1, -1);
						ST[root].LeftChild = nST - 1;
					}
					root = ST[root].LeftChild;
				}else{
					if (ST[root].RightChild == -1){
						AddSearchTrie(-1, -1, -1);
						ST[root].RightChild = nST - 1;
					}
					root = ST[root].RightChild;
				}
				
				aByte /= 2;
			}
			
			ST[root].IsWord = i;
		}
	}
	
	public static void WriteEncryptedFile(BufferedOutputStream file, int word) throws IOException {
		int aByte = word;
		
		for (int i = 0; i < Length; i++){
			stack[top] = aByte % 2;
			SumByte += stack[top] * (1 << top);
			top++;
			if (top == nBitsByte){
				file.write(SumByte);
				top = 0;
				SumByte = 0;
			}
			aByte /= 2;
		}
	}
	
	public static boolean Encrypt(String InputName, String OutputName) throws IOException {
		BufferedInputStream Input = new BufferedInputStream (new FileInputStream(InputName));
		
		if (Input.available() == 0){
			Input.close();
			return false;
		}
		
		BufferedOutputStream Output = new BufferedOutputStream (new FileOutputStream(OutputName));
		
		int start, finish, word, root, aByte, bit, first, second;
		boolean found, CanCreated;
		
		start = Input.read();
		first = 0;
		second = 0;
		
		while (true){
			if (Input.available() == 0){
				WriteEncryptedFile(Output, start);
				break;
			}
		
			CanCreated = false;
			if (nWords + 1 < (1 << LengthLimit)){
				CanCreated = true;
				second = first;
			}
			
			root = 0;
			aByte = start;
			for (int i = 0; i < nBitsByte; i++){
				bit = aByte % 2;
				if (bit == 0)
					root = ST[root].LeftChild;
				else
					root = ST[root].RightChild;
				aByte /= 2;
			}
			word = ST[root].IsWord;
			
			while (Input.available() > 0){
				if (CanCreated) second++;
				finish = Input.read();
				found = true;
				aByte = finish;
				
				for (int i = 0; i < nBitsByte; i++){
					bit = aByte % 2;
					if (bit == 0){
						if (ST[root].LeftChild == -1){
							found = false;
							if (!CanCreated) break;
							AddSearchTrie(-1, -1, -1);
							ST[root].LeftChild = nST - 1;
						}
						root = ST[root].LeftChild;
					}else{
						if (ST[root].RightChild == -1){
							found = false;
							if (!CanCreated) break;
							AddSearchTrie(-1, -1, -1);
							ST[root].RightChild = nST - 1;
						}
						root = ST[root].RightChild;
					}
					aByte /= 2;
				}
				
				if (!found){
					WriteEncryptedFile(Output, word);
					start = finish;
					if (CanCreated){
						First[nWords] = first;
						Second[nWords] = second;
						first = second;
						nWords++;
						if (nWords > (1 << Length)) Length++;
						ST[root].IsWord = nWords - 1;
					}
					break;
				}else{
					word = ST[root].IsWord;
					if (Input.available() == 0)
						WriteEncryptedFile(Output, word);
				}
			}
		}
		
		if (top > 0){
			SumByte = 0;
			for (int j = 0; j < top; j++)
				SumByte += stack[j] * (1 << j);
			Output.write(SumByte);
		}
		
		Input.close();
		Output.close();
		
		return true;
	}
	
	public static void MakeDictionary(int node, int pos, int bit[]){
		int i, j, v;
		
		if (ST[node].IsWord != -1){
			i = ST[node].IsWord;
			Dictionary[i] = new int [pos / nBitsByte];
			j = 0;
			for (v = 0; v < pos; v++){
				Dictionary[i][j] += bit[v] * (1 << (v % nBitsByte));
				if ((v + 1) % nBitsByte == 0) j++;
			}
		}
		
		if (ST[node].LeftChild != -1){
			bit[pos] = 0;
			MakeDictionary(ST[node].LeftChild, pos + 1, bit);
		}
		
		if (ST[node].RightChild != -1){
			bit[pos] = 1;
			MakeDictionary(ST[node].RightChild, pos + 1, bit);
		}
	}
	
	public static void AddDictionary(String InputName, String OutputName, String TempName) throws IOException {
		BufferedInputStream Input = new BufferedInputStream(new FileInputStream(InputName));
		BufferedInputStream Temp = new BufferedInputStream(new FileInputStream(TempName));
		
		BufferedOutputStream Output = new BufferedOutputStream(new FileOutputStream(OutputName));
		
		Output.write(nWords % ByteValue);
		Output.write(nWords / ByteValue);
		
		int len, aByte, last = 0;
		int pos = -1;
		
		for (int i = ByteValue; i < nWords; i++){
			len = Second[i] - First[i] + 1;
			Output.write(len % ByteValue);
			Output.write(len / ByteValue);
			
			while (true){
				if (i == ByteValue){
					aByte = Input.read();
					pos++;
				}else
					aByte = last;
				
				if (pos == First[i]){
					Output.write(aByte);
					break;
				}
			}
			
			while (true){
				aByte = Input.read();
				pos++;
				Output.write(aByte);
				if (pos == Second[i]) break;
			}
			last = aByte;
		}
		
		//MakeDictionary(0, 0, stack);
		
		while (Temp.available() > 0)
			Output.write(Temp.read());
		
		Input.close();
		Output.close();
		Temp.close();
	}
	
	public static void Decrypt(String InputName, String OutputName) throws IOException {
		BufferedInputStream Input = new BufferedInputStream (new FileInputStream(InputName));
		BufferedOutputStream Output = new BufferedOutputStream (new FileOutputStream(OutputName));
		
		nWords = (int)(Input.read()) + (int)(Input.read()) * ByteValue;
		
		for (int i = 0; i < ByteValue; i++){
			Dictionary[i] = new int [1];
			Dictionary[i][0] = i;
		}
		
		int size;
		for (int i = ByteValue; i < nWords; i++){
			size = (int)(Input.read()) + (int)(Input.read()) * ByteValue;
			Dictionary[i] = new int [size];
			for (int j = 0; j < size; j++)
				Dictionary[i][j] = Input.read();
		}
		
		top = 0;
		Length = nBitsByte;
		
		int aByte;
		int count = ByteValue;
		
		SumByte = 0;
		while (Input.available() > 0){
			aByte = Input.read();
			for (int i = 0; i < nBitsByte; i++){
				stack[top] = aByte % 2;
				SumByte += stack[top] * (1 << top);
				top++;
				if (top == Length){
					for (int j = 0; j < Dictionary[SumByte].length; j++)
						Output.write(Dictionary[SumByte][j]);
					SumByte = 0;
					top = 0;
					
					if (count + 1 < (1 << LengthLimit)){
						count++; 
						if (count > (1 << Length)) Length++;
					}
				}
				aByte /= 2;
			}
		}
		
		Input.close();
		Output.close();
	}
	
	public static String GetType(String FileName){
		int i, j;
		String res;
		j = -1;
		for (i = 0; i < FileName.length(); i++)
			if (FileName.charAt(i) == '.'){
				j = i;
				break;
			}
		res = "";
		if (j == -1) return res;
		for (i = j + 1; i < FileName.length(); i++) res += FileName.charAt(i);
		return res;
	}
	
	public static void main(String args[]) throws IOException {
		if (args.length < 2) return;
		
		if (args[0].equals("-e")){
			String InputName = args[1];
			String OutputName = "EncryptedFile";
			if (args.length >= 3)
				OutputName = args[2];
			String type = GetType(InputName);
			if (type.length() > 0)
				OutputName += "." + type;
			String TempName = OutputName + ".temp";
			
			Init();
			
			if (!Encrypt(InputName, TempName))
				System.out.println("[" + InputName + " is an empty file]");
			else{
				AddDictionary(InputName, OutputName, TempName);
				Runtime rt = Runtime.getRuntime();
				//Process pr = rt.exec("rm -r " + TempName);
			}
		}
		
		if (args[0].equals("-d")){
			String InputName = args[1];
			String OutputName = "DecryptedFile";
			if (args.length >= 3)
				OutputName = args[2];
			String type = GetType(InputName);
			if (type.length() > 0)
				OutputName += "." + type;
			
			Decrypt(InputName, OutputName);
		}
	}	
	
}
