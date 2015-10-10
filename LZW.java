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

public class LZW {
	
	static int Byte = 1 << 8;
	static int Max_nSegments = 1 << 20;
	static int Max_BitLength = 12;
	static int Max_nWords = 1 << Max_BitLength;
	static int Max_nTrie = Max_BitLength * (Max_nWords + 1);
	
	static int Max_nProcess = 20000;
	
	static int nSegments, nProcess, nBuff;
	static int Segment[] = new int [Max_nSegments];
	static int Buff[] = new int [Max_nSegments];
	
	static int nWords, BitLength;
	
	static class TrieNode {
		public int IsWord;
		public int next[] = new int [Byte];
	}
	static int nTrie;
	static TrieNode Trie[] = new TrieNode [Max_nTrie];
	
	static int top, SumByte;
	static int BitStack[] = new int [Max_BitLength];
	
	static int Word[][] = new int [Max_nWords][];
	static int Start[] = new int [Max_nWords];
	static int Finish[] = new int [Max_nWords];
	
	public static void AllocateMemory(){
		int i, j;
		for (i = 0; i < Max_nTrie; i++){
			Trie[i] = new TrieNode();
			for (j = 0; j < Byte; j++)
				Trie[i].next[j] = 0;
		}
	}
	
	public static void ResetTrie(){
		int i, j;
		for (i = 0; i < Max_nTrie; i++)
			for (j = 0; j < Byte; j++)
				Trie[i].next[j] = 0;
	}
	
	public static void Init(){
		BitLength = 8;
		
		Trie[0].IsWord = -1;
		nTrie = 1;
		nWords = 0;
		top = 0;
		SumByte = 0;
		nBuff = 0;
		
		int root = 0;
		
		for (int i = 0; i < Byte; i++){
			nTrie++;
			nWords++;
			Trie[nTrie - 1].IsWord = nWords - 1;
			Trie[root].next[i] = nProcess * Max_nTrie + nTrie - 1;
		}
	}
	
	public static void UpdateBuffer(int word) throws IOException {
		int i;
		for (i = 0; i < BitLength; i++){
			BitStack[top] = word % 2;
			SumByte += BitStack[top] * (1 << top);
			top++;
			if (top == 8){
				Buff[nBuff] = SumByte;
				nBuff++;
				SumByte = 0;
				top = 0;
			}
			word /= 2;
		}
	}
	
	public static void WriteBuffer(BufferedOutputStream Output) throws IOException {
		int i, j, length;
		
		Output.write(nWords % Byte);
		Output.write(nWords / Byte);			
		
		for (i = Byte; i < nWords; i++){
			length = Finish[i] - Start[i] + 1;
			Output.write(length % Byte);
			Output.write(length / Byte);
			
			for (j = Start[i]; j <= Finish[i]; j++)
				Output.write(Segment[j]);
		}
		
		i = nBuff;
		int nBytes = 0;
		while (i > 0){
			nBytes++;
			i /= Byte;
		}
		
		Output.write(nBytes);
		i = nBuff;
		for (j = 0; j < nBytes; j++){
			Output.write(i % Byte);
			i /= Byte;
		}
		
		for (i = 0; i < nBuff; i++)
			Output.write(Buff[i]);
	}
	
	public static void Encrypt(BufferedOutputStream Output) throws IOException {
		int i, j, v, root;
		
		Init();
		
		i = 0;
		while (i < nSegments){
			root = 0;
			v = i;
			
			for (j = i; j < nSegments; j++){
				if (Trie[root].next[Segment[j]] <= nProcess * Max_nTrie){
					UpdateBuffer(Trie[root].IsWord);
					
					if (nWords + 1 <= Max_nWords){
						nTrie++;
						nWords++;
						
						Trie[nTrie - 1].IsWord = nWords - 1;
						Trie[root].next[Segment[j]] = nProcess * Max_nTrie + nTrie - 1;
						
						Start[nWords - 1] = i;
						Finish[nWords - 1] = j;
						
						if (nWords > 1 << BitLength)
							BitLength++;
					}	
					break;
				}
				
				root = Trie[root].next[Segment[j]] - nProcess * Max_nTrie;
				v = j;
			}
			
			if (v == nSegments - 1)
				UpdateBuffer(Trie[root].IsWord);
			
			i = v + 1;
		}
		
		if (top > 0){
			SumByte = 0;
			for (i = 0; i < top; i++) SumByte+= BitStack[i] * (1 << i);
			Buff[nBuff] = SumByte;
			nBuff++;
		}
		
		WriteBuffer(Output);
	}
	
	public static void EncryptionNotice(){
		System.out.println("[Process " + nProcess + ": Completed encryption process for one " + nSegments + "-byte segment]");
	}
	
	public static boolean Encrypt(String InputName, String OutputName) throws IOException {
		int aByte;
		BufferedInputStream Input = new BufferedInputStream(new FileInputStream(InputName));
		
		if (Input.available() == 0){
			Input.close();
			return false;
		}
		
		BufferedOutputStream Output = new BufferedOutputStream(new FileOutputStream(OutputName));
		
		AllocateMemory();
		
		nProcess = 0;
		nSegments = 0;
		while (Input.available() > 0){
			Segment[nSegments] = Input.read();
			nSegments++;
			if (nSegments == Max_nSegments){
				Encrypt(Output);
				EncryptionNotice();
				nSegments = 0;
				nProcess++;
				
				if ((nProcess == Max_nProcess) && (Input.available() > 0)){
					nProcess = 0;
					ResetTrie();
				}
			}
		}
		
		if (nSegments > 0){
			Encrypt(Output);
			EncryptionNotice();
		}
		
		Input.close();
		Output.close();
		
		return true;
	}
	
	public static void ReadSegment(BufferedInputStream Input, BufferedOutputStream Output) throws IOException {
		int i, j, v, length, aByte, counting;
		boolean stop;
		
		nWords = Input.read() + Input.read() * Byte;
		
		for (i = 0; i < Byte; i++){
			Word[i] = new int [1];
			Word[i][0] = i;
		}
		
		for (i = Byte; i < nWords; i++){
			length = Input.read() + Input.read() * Byte;
			Word[i] = new int [length];
			for (j = 0; j < Word[i].length; j++)
				Word[i][j] = Input.read();
		}
		
		int nBytes = Input.read();
		
		nBuff = 0;
		for (i = 0; i < nBytes; i++)
			nBuff += Input.read() * (1 << (8 * i));
		
		BitLength = 8;
		top = 0;
		SumByte = 0;
		counting = Byte;
		stop = false;
		
		int t = 0;
		
		for (v = 0; v < nBuff; v++){
			aByte = Input.read();
			
			for (i = 0; i < 8; i++){
				SumByte += (aByte % 2) * (1 << top);
				aByte /= 2;
				top++;
				
				if (top == BitLength){
					if (counting < Max_nWords){
						counting++;
						if (counting > 1 << BitLength)
							BitLength++;
					}
					
					for (j = 0; j < Word[SumByte].length; j++)
						Output.write(Word[SumByte][j]);
						
					top = 0;
					SumByte = 0;
				}
			}
		}
	}
	
	public static void Decrypt(String InputName, String OutputName) throws IOException {
		BufferedInputStream Input = new BufferedInputStream(new FileInputStream(InputName));
		BufferedOutputStream Output = new BufferedOutputStream(new FileOutputStream(OutputName));
		
		while (true){
			if (Input.available() == 0) break;
			ReadSegment(Input, Output);
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
			String OutputName = args[2];
			
			if (!Encrypt(InputName, OutputName))
				System.out.println("[" + InputName + " is an empty file]");
		}
		
		if (args[0].equals("-d")){
			String InputName = args[1];
			String OutputName = args[2];
				
			Decrypt(InputName, OutputName);
		}
	}	
	
}
