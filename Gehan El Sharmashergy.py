import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext
from base64 import b64encode, b64decode
import re

# ========================= RC4 (CR4) CIPHER FUNCTIONS =========================
def cr4_keystream(length, key):
    S = list(range(8))
    j = 0
    for i in range(8):
        j = (j + S[i] + key[i % len(key)]) % 8
        S[i], S[j] = S[j], S[i]
    i = j = 0
    stream = []
    for _ in range(length):
        i = (i + 1) % 8
        j = (j + S[i]) % 8
        S[i], S[j] = S[j], S[i]
        K = S[(S[i] + S[j]) % 8]
        stream.append(K)
    return stream

def cr4_encrypt(data, key):
    stream = cr4_keystream(len(data), key)
    return [d ^ k for d, k in zip(data, stream)]

def text_to_3bit_blocks(text):
    bits = ''.join(f'{ord(c):08b}' for c in text)
    return [int(bits[i:i+3], 2) for i in range(0, len(bits), 3)]

def blocks_to_text(blocks):
    bits = ''.join(f'{b:03b}' for b in blocks)
    chars = [chr(int(bits[i:i+8], 2)) for i in range(0, len(bits), 8)]
    return ''.join(chars).rstrip('\x00')

# ============================ END RC4 FUNCTIONS ==============================


# ============================== RSA FUNCTIONS ================================
def is_prime(n):
    if n < 2: return False
    for i in range(2, int(n**0.5)+1):
        if n % i == 0: return False
    return True

def gcd(a, b):
    while b: a, b = b, a % b
    return a

def modinv(e, phi):
    for d in range(1, phi):
        if (d * e) % phi == 1: return d
    return None

def rsa_generate_keys(p, q):
    if not (is_prime(p) and is_prime(q)): raise ValueError("Both p and q must be prime.")
    if p == q: raise ValueError("p and q cannot be the same.")
    n = p * q
    phi = (p - 1) * (q - 1)
    e = next(i for i in range(2, phi) if gcd(i, phi) == 1)
    d = modinv(e, phi)
    if d is None:
        raise RuntimeError("Failed to find modular inverse.")
    return (e, n), (d, n)

def rsa_encrypt_int(m, public_key):
    e, n = public_key
    if not (0 <= m < n):
        raise ValueError(f"Integer must be between 0 and n-1 (n={n}).")
    return pow(m, e, n)

def rsa_decrypt_int(c, private_key):
    d, n = private_key
    return pow(c, d, n)

def rsa_encrypt_text(text, pub_key):
    return [rsa_encrypt_int(b, pub_key) for b in text.encode('utf-8')]

def rsa_decrypt_text(cipher, priv_key):
    decrypted = [rsa_decrypt_int(c, priv_key) for c in cipher]
    return bytearray(decrypted).decode('utf-8', errors='replace')

# ============================ END RSA FUNCTIONS ==============================


# ============================== SHA-256 FUNCTIONS ==============================
K = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
]

def right_rotate(n, b):
    return ((n >> b) | (n << (32 - b))) & 0xffffffff

def sha256(message):
    # Convert the message to a byte array
    message = bytearray(message.encode('utf-8'))
    # Save original length in bits
    orig_len_in_bits = (8 * len(message)) & 0xffffffffffffffff
    # Add a single 1 bit
    message.append(0x80)
    while (len(message) * 8 + 64) % 512 != 0:
        message.append(0)
    # Append original length at the end (64 bits)
    message += orig_len_in_bits.to_bytes(8, 'big')

    # Initial hash values
    h0 = 0x6a09e667
    h1 = 0xbb67ae85
    h2 = 0x3c6ef372
    h3 = 0xa54ff53a
    h4 = 0x510e527f
    h5 = 0x9b05688c
    h6 = 0x1f83d9ab
    h7 = 0x5be0cd19

    for i in range(0, len(message), 64):
        chunk = message[i:i+64]
        # Create a list of 64 32-bit words
        w = [int.from_bytes(chunk[j:j+4], 'big') for j in range(0, 64, 4)]

        for j in range(16, 64):
            s0 = right_rotate(w[j-15], 7) ^ right_rotate(w[j-15], 18) ^ (w[j-15] >> 3)
            s1 = right_rotate(w[j-2], 17) ^ right_rotate(w[j-2], 19) ^ (w[j-2] >> 10)
            w.append((w[j-16] + s0 + w[j-7] + s1) & 0xffffffff)

        # Initialize working variables
        a, b, c, d, e, f, g, h = h0, h1, h2, h3, h4, h5, h6, h7

        for j in range(64):
            S1 = right_rotate(e, 6) ^ right_rotate(e, 11) ^ right_rotate(e, 25)
            ch = (e & f) ^ (~e & g)
            temp1 = (h + S1 + ch + K[j] + w[j]) & 0xffffffff
            S0 = right_rotate(a, 2) ^ right_rotate(a, 13) ^ right_rotate(a, 22)
            maj = (a & b) ^ (a & c) ^ (b & c)
            temp2 = (S0 + maj) & 0xffffffff

            # Update variables
            h = g
            g = f
            f = e
            e = (d + temp1) & 0xffffffff
            d = c
            c = b
            b = a
            a = (temp1 + temp2) & 0xffffffff

        h0 = (h0 + a) & 0xffffffff
        h1 = (h1 + b) & 0xffffffff
        h2 = (h2 + c) & 0xffffffff
        h3 = (h3 + d) & 0xffffffff
        h4 = (h4 + e) & 0xffffffff
        h5 = (h5 + f) & 0xffffffff
        h6 = (h6 + g) & 0xffffffff
        h7 = (h7 + h) & 0xffffffff

    return ''.join(format(x, '08x') for x in [h0, h1, h2, h3, h4, h5, h6, h7])

# ============================ END SHA-256 FUNCTIONS ==============================


# ============================== AES-CFB FUNCTIONS ==============================
class AES_CFB:
    # AES S-box
    SBOX = [
        0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
        0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
        0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
        0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
        0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
        0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
        0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
        0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
        0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
        0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
        0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
        0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
        0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
        0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
        0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
        0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16
    ]

    # AES Inverse S-box
    INV_SBOX = [
        0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
        0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb,
        0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
        0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25,
        0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
        0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84,
        0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
        0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b,
        0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,
        0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85, 0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e,
        0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
        0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4,
        0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
        0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef,
        0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
        0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d
    ]

    # Rijndael Rcon
    RCON = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36]

    def __init__(self, key, iv):
        if len(key) not in [16, 24, 32]:
            raise ValueError("Key must be 16, 24, or 32 bytes long")
        if len(iv) != 16:
            raise ValueError("IV must be 16 bytes for AES")
        
        self.key = key
        self.iv = iv
        self.n_rounds = {16: 10, 24: 12, 32: 14}[len(key)]
        self.round_keys = self.key_expansion()

    def key_expansion(self):
        n_k = len(self.key) // 4
        round_keys = [0] * (4 * (self.n_rounds + 1))
        
        for i in range(n_k):
            round_keys[i] = (self.key[4*i] << 24) | (self.key[4*i+1] << 16) | \
                           (self.key[4*i+2] << 8) | self.key[4*i+3]
        
        for i in range(n_k, 4 * (self.n_rounds + 1)):
            temp = round_keys[i-1]
            
            if i % n_k == 0:
                temp = self.sub_word(self.rot_word(temp)) ^ (self.RCON[i//n_k - 1] << 24)
            elif n_k > 6 and i % n_k == 4:
                temp = self.sub_word(temp)
            
            round_keys[i] = round_keys[i - n_k] ^ temp
        
        return round_keys

    @staticmethod
    def rot_word(word):
        return ((word << 8) | (word >> 24)) & 0xFFFFFFFF

    @staticmethod
    def sub_word(word):
        return (AES_CFB.SBOX[(word >> 24) & 0xFF] << 24) | \
               (AES_CFB.SBOX[(word >> 16) & 0xFF] << 16) | \
               (AES_CFB.SBOX[(word >> 8) & 0xFF] << 8) | \
               AES_CFB.SBOX[word & 0xFF]

    def pad(self, data):
        pad_len = 16 - (len(data) % 16)
        return data + bytes([pad_len] * pad_len)

    def unpad(self, data):
        pad_len = data[-1]
        if pad_len > 16:
            raise ValueError("Invalid padding")
        return data[:-pad_len]

    def aesencrypt(self, plaintext):
        ciphertext = b''
        prev_block = self.iv
        plaintext = self.pad(plaintext)
        
        for i in range(0, len(plaintext), 16):
            block = plaintext[i:i+16]
            keystream = self.encrypt_block(prev_block)
            cipher_block = bytes([a ^ b for a, b in zip(block, keystream)])
            ciphertext += cipher_block
            prev_block = cipher_block
        
        return ciphertext

    def aesdecrypt(self, ciphertext):
        plaintext = b''
        prev_block = self.iv
        
        for i in range(0, len(ciphertext), 16):
            block = ciphertext[i:i+16]
            keystream = self.encrypt_block(prev_block)
            plain_block = bytes([a ^ b for a, b in zip(block, keystream)])
            plaintext += plain_block
            prev_block = block
        
        return self.unpad(plaintext)

    def encrypt_block(self, block):
        state = [[0]*4 for _ in range(4)]
        
        for i in range(4):
            for j in range(4):
                state[j][i] = block[i*4 + j]
        
        self.add_round_key(state, 0)
        
        for round in range(1, self.n_rounds):
            self.sub_bytes(state)
            self.shift_rows(state)
            self.mix_columns(state)
            self.add_round_key(state, round)
        
        self.sub_bytes(state)
        self.shift_rows(state)
        self.add_round_key(state, self.n_rounds)
        
        output = bytearray(16)
        for i in range(4):
            for j in range(4):
                output[i*4 + j] = state[j][i]
        
        return bytes(output)

    def sub_bytes(self, state):
        for i in range(4):
            for j in range(4):
                state[i][j] = self.SBOX[state[i][j]]

    def shift_rows(self, state):
        state[1][0], state[1][1], state[1][2], state[1][3] = \
            state[1][1], state[1][2], state[1][3], state[1][0]
        state[2][0], state[2][1], state[2][2], state[2][3] = \
            state[2][2], state[2][3], state[2][0], state[2][1]
        state[3][0], state[3][1], state[3][2], state[3][3] = \
            state[3][3], state[3][0], state[3][1], state[3][2]

    def mix_columns(self, state):
        for i in range(4):
            s0 = state[0][i]
            s1 = state[1][i]
            s2 = state[2][i]
            s3 = state[3][i]
            
            state[0][i] = self.xtime(s0) ^ self.xtime(s1) ^ s1 ^ s2 ^ s3
            state[1][i] = s0 ^ self.xtime(s1) ^ self.xtime(s2) ^ s2 ^ s3
            state[2][i] = s0 ^ s1 ^ self.xtime(s2) ^ self.xtime(s3) ^ s3
            state[3][i] = self.xtime(s0) ^ s0 ^ s1 ^ s2 ^ self.xtime(s3)

    @staticmethod
    def xtime(x, n=1):
        result = x
        for _ in range(n):
            result = ((result << 1) ^ 0x1B) & 0xFF if (result & 0x80) else (result << 1)
        return result

    def add_round_key(self, state, round):
        for i in range(4):
            word = self.round_keys[round*4 + i]
            state[0][i] ^= (word >> 24) & 0xFF
            state[1][i] ^= (word >> 16) & 0xFF
            state[2][i] ^= (word >> 8) & 0xFF
            state[3][i] ^= word & 0xFF

# ============================ END AES-CFB FUNCTIONS ==============================


# ============================== DES FUNCTIONS ==============================
IP = [58,50,42,34,26,18,10,2,60,52,44,36,28,20,12,4,
      62,54,46,38,30,22,14,6,64,56,48,40,32,24,16,8,
      57,49,41,33,25,17,9,1,59,51,43,35,27,19,11,3,
      61,53,45,37,29,21,13,5,63,55,47,39,31,23,15,7]
IP_INV = [40,8,48,16,56,24,64,32,39,7,47,15,55,23,63,31,
          38,6,46,14,54,22,62,30,37,5,45,13,53,21,61,29,
          36,4,44,12,52,20,60,28,35,3,43,11,51,19,59,27,
          34,2,42,10,50,18,58,26,33,1,41,9,49,17,57,25]
E = [32,1,2,3,4,5,4,5,6,7,8,9,8,9,10,11,12,13,
     12,13,14,15,16,17,16,17,18,19,20,21,20,21,22,23,24,25,
     24,25,26,27,28,29,28,29,30,31,32,1]
S_BOX = [
  # S1
  [[14,4,13,1,2,15,11,8,3,10,6,12,5,9,0,7],
   [0,15,7,4,14,2,13,1,10,6,12,11,9,5,3,8],
   [4,1,14,8,13,6,2,11,15,12,9,7,3,10,5,0],
   [15,12,8,2,4,9,1,7,5,11,3,14,10,0,6,13]],
  # S2
  [[15,1,8,14,6,11,3,4,9,7,2,13,12,0,5,10],
   [3,13,4,7,15,2,8,14,12,0,1,10,6,9,11,5],
   [0,14,7,11,10,4,13,1,5,8,12,6,9,3,2,15],
   [13,8,10,1,3,15,4,2,11,6,7,12,0,5,14,9]],
  # S3
  [[10,0,9,14,6,3,15,5,1,13,12,7,11,4,2,8],
   [13,7,0,9,3,4,6,10,2,8,5,14,12,11,15,1],
   [13,6,4,9,8,15,3,0,11,1,2,12,5,10,14,7],
   [1,10,13,0,6,9,8,7,4,15,14,3,11,5,2,12]],
  # S4
  [[7,13,14,3,0,6,9,10,1,2,8,5,11,12,4,15],
   [13,8,11,5,6,15,0,3,4,7,2,12,1,10,14,9],
   [10,6,9,0,12,11,7,13,15,1,3,14,5,2,8,4],
   [3,15,0,6,10,1,13,8,9,4,5,11,12,7,2,14]],
  # S5
  [[2,12,4,1,7,10,11,6,8,5,3,15,13,0,14,9],
   [14,11,2,12,4,7,13,1,5,0,15,10,3,9,8,6],
   [4,2,1,11,10,13,7,8,15,9,12,5,6,3,0,14],
   [11,8,12,7,1,14,2,13,6,15,0,9,10,4,5,3]],
  # S6
  [[12,1,10,15,9,2,6,8,0,13,3,4,14,7,5,11],
   [10,15,4,2,7,12,9,5,6,1,13,14,0,11,3,8],
   [9,14,15,5,2,8,12,3,7,0,4,10,1,13,11,6],
   [4,3,2,12,9,5,15,10,11,14,1,7,6,0,8,13]],
  # S7
  [[4,11,2,14,15,0,8,13,3,12,9,7,5,10,6,1],
   [13,0,11,7,4,9,1,10,14,3,5,12,2,15,8,6],
   [1,4,11,13,12,3,7,14,10,15,6,8,0,5,9,2],
   [6,11,13,8,1,4,10,7,9,5,0,15,14,2,3,12]],
  # S8
  [[13,2,8,4,6,15,11,1,10,9,3,14,5,0,12,7],
   [1,15,13,8,10,3,7,4,12,5,6,11,0,14,9,2],
   [7,11,4,1,9,12,14,2,0,6,10,13,15,3,5,8],
   [2,1,14,7,4,10,8,13,15,12,9,0,3,5,6,11]],
]
P  = [16,7,20,21,29,12,28,17, 1,15,23,26,5,18,31,10,
      2,8,24,14,32,27,3,9, 19,13,30,6,22,11,4,25]
PC1= [57,49,41,33,25,17,9,1,58,50,42,34,26,18,
      10,2,59,51,43,35,27,19,11,3,60,52,44,36,
      63,55,47,39,31,23,15,7,62,54,46,38,30,22,
      14,6,61,53,45,37,29,21,13,5,28,20,12,4]
PC2= [14,17,11,24,1,5,3,28,15,6,21,10,23,19,12,4,
      26,8,16,7,27,20,13,2,41,52,31,37,47,55,30,40,
      51,45,33,48,44,49,39,56,34,53,46,42,50,36,29,32]
SHIFTS = [1,1,2,2,2,2,2,2,1,2,2,2,2,2,2,1]

# Helper functions for DES
def _permute(b, t): return [b[i-1] for i in t]
def _lrot(l,n):  return l[n:]+l[:n]
def _str2bits(s): return [int(x) for ch in s for x in format(ord(ch),'08b')]
def _bits2hex(b): return ''.join(f"{byte:02x}" for byte in
                                 bytes(int(''.join(str(bit) for bit in b[i:i+8]),2)
                                       for i in range(0,len(b),8)) )

def _gen_keys(key8):
    kb = _str2bits(key8)
    k56 = _permute(kb, PC1)
    C, D = k56[:28], k56[28:]
    rounds = []
    for sh in SHIFTS:
        C,D = _lrot(C,sh), _lrot(D,sh)
        rounds.append(_permute(C+D,PC2))
    return rounds

def _feistel(R, K):
    ER = _permute(R, E)
    X  = [e^k for e,k in zip(ER,K)]
    out = []
    for i in range(8):
        blk = X[6*i:6*i+6]
        row = (blk[0]<<1)|blk[5]
        col = (blk[1]<<3)|(blk[2]<<2)|(blk[3]<<1)|blk[4]
        val = S_BOX[i][row][col]
        out += [int(bit) for bit in format(val,'04b')]
    return _permute(out, P)

def _des_block(block, keys, enc=True):
    if isinstance(block, list):  # already bits
        bits = _permute(block, IP)
    else:
        bits = _permute(_str2bits(block), IP)
    L, R = bits[:32], bits[32:]
    ks = keys if enc else list(reversed(keys))
    for K in ks:
        L, R = R, [l^f for l,f in zip(L,_feistel(R,K))]
    return _permute(R+L, IP_INV)

def des_encrypt(key, txt):
    if len(key) != 8:
        raise ValueError("Key must be 8 characters")
    pad = 8 - len(txt) % 8
    txt += chr(pad) * pad
    keys = _gen_keys(key)
    res = []
    for i in range(0, len(txt), 8):
        bits = _des_block(txt[i:i+8], keys, True)
        res.append(_bits2hex(bits))
    return ''.join(res)

def des_decrypt(key, hexct):
    if len(key) != 8:
        raise ValueError("Key must be 8 characters")
    keys = _gen_keys(key)
    plain = ''
    for i in range(0, len(hexct), 16):
        chunk = hexct[i:i+16]
        bits = []
        for j in range(0, 16, 2):
            byte = int(chunk[j:j+2], 16)
            bits += [int(b) for b in format(byte, '08b')]
        dec = _des_block(bits, keys, False)
        block = bytes(int(''.join(map(str, dec[k:k+8])), 2)
                      for k in range(0, 64, 8)).decode('latin-1')
        plain += block
    return plain[:-ord(plain[-1])]

# ============================ END DES FUNCTIONS ==============================


# ============================== GUI CLASS ====================================
class EncryptionGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("Gehan El Shamashergy")
        self.root.geometry("1000x700")
        self.algorithm = tk.StringVar(value="")

        self.sidebar_buttons = []
        self.public_key = None
        self.private_key = None

        self.setup_sidebar()
        self.setup_main_frame()

    def setup_sidebar(self):
        sidebar = tk.Frame(self.root, bg="#eeeeee", width=120)
        sidebar.pack(side=tk.LEFT, fill=tk.Y)

        for algo in ["RC4", "RSA", "SHA-256", "AES-CFB", "DES"]:
            btn = tk.Button(sidebar, text=algo, width=12, pady=10,
                          bg="#f0f0f0", relief="flat",
                          command=lambda a=algo: self.select_algorithm(a))
            btn.pack(pady=5)
            btn.bind("<Enter>", lambda e, b=btn: b.config(bg="#cce6ff"))
            btn.bind("<Leave>", lambda e, b=btn: b.config(bg="#f0f0f0"))
            self.sidebar_buttons.append(btn)

    def setup_main_frame(self):
        self.main_frame = tk.Frame(self.root, bg="white")
        self.main_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=20, pady=20)

    def select_algorithm(self, algo):
        self.algorithm.set(algo)
        for btn in self.sidebar_buttons:
            if btn["text"] == algo:
                btn.config(bg="#3399ff", fg="white")
            else:
                btn.config(bg="#f0f0f0", fg="black")

        for widget in self.main_frame.winfo_children():
            widget.destroy()

        if algo == "RC4":
            self.load_cr4_form()
        elif algo == "RSA":
            self.load_rsa_form()
        elif algo == "SHA-256":
            self.load_sha256_form()
        elif algo == "AES-CFB":
            self.load_aes_cfb_form()
        elif algo == "DES":
            self.load_des_form()
        else:
            tk.Label(self.main_frame, text=f"{algo} interface coming soon!",
                   font=("Arial", 14), bg="white").pack()

    # --------------------------- RC4 GUI HANDLING ---------------------------
    def load_cr4_form(self):
        frame_main = tk.LabelFrame(self.main_frame, text="RC4 Cipher", padx=10, pady=10, bg="white")
        frame_main.pack(fill="both", expand=True)

        frame_input = tk.Frame(frame_main, bg="white")
        frame_input.pack(fill="x", padx=10, pady=5)

        # Mode selection
        tk.Label(frame_input, text="Mode:", bg="white").grid(row=0, column=0, sticky="e", padx=5, pady=5)
        self.cr4_mode_var = tk.StringVar(value="String")
        mode_menu = ttk.Combobox(frame_input, textvariable=self.cr4_mode_var, 
                                values=["String", "Numerical"], state="readonly", width=20)
        mode_menu.grid(row=0, column=1, pady=5, sticky="w")

        # Input fields
        tk.Label(frame_input, text="Plaintext or Ciphertext:", bg="white").grid(row=1, column=0, sticky="e", padx=5, pady=5)
        self.cr4_plain_entry = ttk.Entry(frame_input, width=50)
        self.cr4_plain_entry.grid(row=1, column=1, pady=5, sticky="w")

        tk.Label(frame_input, text="Key (space-separated 0-7):", bg="white").grid(row=2, column=0, sticky="e", padx=5, pady=5)
        self.cr4_key_entry = ttk.Entry(frame_input, width=50)
        self.cr4_key_entry.grid(row=2, column=1, pady=5, sticky="w")

        # Buttons
        frame_buttons = tk.Frame(frame_main, bg="white")
        frame_buttons.pack(pady=10)

        tk.Button(frame_buttons, text="Encrypt", command=self.run_cr4_encrypt, 
                 bg="#4CAF50", fg="white", width=12).pack(side=tk.LEFT, padx=5)
        tk.Button(frame_buttons, text="Decrypt", command=self.run_cr4_decrypt, 
                 bg="#f44336", fg="white", width=12).pack(side=tk.LEFT, padx=5)
        tk.Button(frame_buttons, text="Clear", command=self.clear_cr4_fields, 
                 width=12).pack(side=tk.LEFT, padx=5)

        # Output frame
        frame_output = tk.LabelFrame(frame_main, text="Results", padx=10, pady=10, bg="white")
        frame_output.pack(fill="both", expand=True, padx=10, pady=5)

        tk.Label(frame_output, text="Ciphertext:", bg="white").grid(row=0, column=0, sticky="w")
        self.cr4_cipher_var = tk.StringVar()
        tk.Entry(frame_output, textvariable=self.cr4_cipher_var, state="readonly", width=50).grid(row=0, column=1, sticky="ew", pady=5)

        tk.Label(frame_output, text="Decrypted Text:", bg="white").grid(row=1, column=0, sticky="w")
        self.cr4_decrypt_var = tk.StringVar()
        tk.Entry(frame_output, textvariable=self.cr4_decrypt_var, state="readonly", width=50).grid(row=1, column=1, sticky="ew", pady=5)

        frame_output.grid_columnconfigure(1, weight=1)

    def run_cr4_encrypt(self):
        self.process_cr4(encrypt=True)

    def run_cr4_decrypt(self):
        self.process_cr4(encrypt=False)

    def clear_cr4_fields(self):
        self.cr4_plain_entry.delete(0, tk.END)
        self.cr4_key_entry.delete(0, tk.END)
        self.cr4_cipher_var.set("")
        self.cr4_decrypt_var.set("")

    def process_cr4(self, encrypt=True):
        key_input = self.cr4_key_entry.get()
        data_input = self.cr4_plain_entry.get()
        mode = self.cr4_mode_var.get()

        try:
            key = [int(x) for x in key_input.strip().split()]
            if any(k < 0 or k > 7 for k in key):
                raise ValueError("Key must be 3-bit numbers (0-7)")

            if mode == "String":
                data = text_to_3bit_blocks(data_input)
            else:
                data = [int(x) for x in data_input.strip().split()]
                if any(d < 0 or d > 7 for d in data):
                    raise ValueError("Plaintext/ciphertext must be 3-bit numbers (0-7)")

            if encrypt:
                cipher = cr4_encrypt(data, key)
                self.cr4_cipher_var.set(" ".join(str(x) for x in cipher))
                if mode == "String":
                    self.cr4_decrypt_var.set(blocks_to_text(cr4_encrypt(cipher, key)))
                else:
                    self.cr4_decrypt_var.set(" ".join(str(x) for x in cr4_encrypt(cipher, key)))
            else:
                decrypted = cr4_encrypt(data, key)
                self.cr4_cipher_var.set(" ".join(str(x) for x in data))
                if mode == "String":
                    self.cr4_decrypt_var.set(blocks_to_text(decrypted))
                else:
                    self.cr4_decrypt_var.set(" ".join(str(x) for x in decrypted))
        except Exception as e:
            messagebox.showerror("Error", str(e))

    # --------------------------- RSA GUI HANDLING ---------------------------
    def load_rsa_form(self):
        frame_main = tk.LabelFrame(self.main_frame, text="RSA Cipher", padx=10, pady=10, bg="white")
        frame_main.pack(fill="both", expand=True)

        frame_input = tk.Frame(frame_main, bg="white")
        frame_input.pack(fill="x", padx=10, pady=5)

        # Input fields
        tk.Label(frame_input, text="Prime p:", bg="white").grid(row=0, column=0, sticky="w", padx=5, pady=5)
        self.p_var = tk.StringVar()
        tk.Entry(frame_input, textvariable=self.p_var).grid(row=0, column=1, sticky="ew", pady=5)

        tk.Label(frame_input, text="Prime q:", bg="white").grid(row=1, column=0, sticky="w", padx=5, pady=5)
        self.q_var = tk.StringVar()
        tk.Entry(frame_input, textvariable=self.q_var).grid(row=1, column=1, sticky="ew", pady=5)

        tk.Label(frame_input, text="Message:", bg="white").grid(row=2, column=0, sticky="w", padx=5, pady=5)
        self.rsa_msg_var = tk.StringVar()
        tk.Entry(frame_input, textvariable=self.rsa_msg_var, width=50).grid(row=2, column=1, sticky="ew", pady=5)

        # Buttons
        frame_buttons = tk.Frame(frame_main, bg="white")
        frame_buttons.pack(pady=10)

        tk.Button(frame_buttons, text="Generate Keys", command=self.generate_rsa_keys, 
                 bg="#4CAF50", fg="white").pack(side="left", padx=5)
        tk.Button(frame_buttons, text="Encrypt", command=self.encrypt_rsa, 
                 bg="#2196F3", fg="white").pack(side="left", padx=5)
        tk.Button(frame_buttons, text="Decrypt", command=self.decrypt_rsa, 
                 bg="#f44336", fg="white").pack(side="left", padx=5)
        tk.Button(frame_buttons, text="Clear", command=self.clear_rsa_fields).pack(side="left", padx=5)

        # Output frame
        frame_output = tk.LabelFrame(frame_main, text="Results", padx=10, pady=10, bg="white")
        frame_output.pack(fill="both", expand=True, padx=10, pady=5)

        tk.Label(frame_output, text="Public Key:", bg="white").grid(row=0, column=0, sticky="w")
        self.pub_var = tk.StringVar()
        tk.Entry(frame_output, textvariable=self.pub_var, state="readonly", width=50).grid(row=0, column=1, sticky="ew", pady=5)

        tk.Label(frame_output, text="Private Key:", bg="white").grid(row=1, column=0, sticky="w")
        self.priv_var = tk.StringVar()
        tk.Entry(frame_output, textvariable=self.priv_var, state="readonly", width=50).grid(row=1, column=1, sticky="ew", pady=5)

        tk.Label(frame_output, text="Output:", bg="white").grid(row=2, column=0, sticky="w")
        self.rsa_result_var = tk.StringVar()
        tk.Entry(frame_output, textvariable=self.rsa_result_var, state="readonly", width=50).grid(row=2, column=1, sticky="ew", pady=5)

        frame_output.grid_columnconfigure(1, weight=1)

    def generate_rsa_keys(self):
        try:
            p = int(self.p_var.get())
            q = int(self.q_var.get())
            self.public_key, self.private_key = rsa_generate_keys(p, q)
            self.pub_var.set(str(self.public_key))
            self.priv_var.set(str(self.private_key))
            self.rsa_result_var.set("")
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def encrypt_rsa(self):
        try:
            if not self.public_key:
                raise ValueError("Generate keys first.")
            msg = self.rsa_msg_var.get()
            if msg.isdigit():
                # If message is just a number, encrypt as integer
                cipher = rsa_encrypt_int(int(msg), self.public_key)
                self.rsa_result_var.set(str(cipher))
            else:
                # Otherwise encrypt as text
                cipher_list = rsa_encrypt_text(msg, self.public_key)
                self.rsa_result_var.set(' '.join(map(str, cipher_list)))
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def decrypt_rsa(self):
        try:
            if not self.private_key:
                raise ValueError("Generate keys first.")
            msg = self.rsa_msg_var.get()
            if msg.isdigit():
                # If message is just a number, decrypt as integer
                plain = rsa_decrypt_int(int(msg), self.private_key)
                self.rsa_result_var.set(str(plain))
            else:
                # Otherwise decrypt as text
                cipher_list = list(map(int, msg.strip().split()))
                plain_text = rsa_decrypt_text(cipher_list, self.private_key)
                self.rsa_result_var.set(plain_text)
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def clear_rsa_fields(self):
        self.p_var.set("")
        self.q_var.set("")
        self.rsa_msg_var.set("")
        self.pub_var.set("")
        self.priv_var.set("")
        self.rsa_result_var.set("")

    # --------------------------- SHA-256 GUI HANDLING ---------------------------
    def load_sha256_form(self):
        frame_main = tk.LabelFrame(self.main_frame, text="SHA-256 Hash", padx=10, pady=10, bg="white")
        frame_main.pack(fill="both", expand=True)

        frame_input = tk.Frame(frame_main, bg="white")
        frame_input.pack(fill="x", padx=10, pady=10)

        tk.Label(frame_input, text="Input Text:", bg="white").grid(row=0, column=0, sticky="w", padx=5, pady=5)
        self.sha256_input_var = tk.StringVar()
        entry = tk.Entry(frame_input, textvariable=self.sha256_input_var, width=60, font=("Courier", 12))
        entry.grid(row=0, column=1, sticky="ew", pady=5)

        # Button to compute hash
        frame_buttons = tk.Frame(frame_main, bg="white")
        frame_buttons.pack(pady=10)

        tk.Button(frame_buttons, text="Generate Hash", command=self.compute_sha256, 
                 font=("Arial", 12), bg="lightblue").pack(side="left", padx=5)
        tk.Button(frame_buttons, text="Clear", command=self.clear_sha256_fields).pack(side="left", padx=5)

        # Output frame
        frame_output = tk.LabelFrame(frame_main, text="Hash Result", padx=10, pady=10, bg="white")
        frame_output.pack(fill="both", expand=True, padx=10, pady=5)

        self.sha256_result_var = tk.StringVar()
        result_label = tk.Label(frame_output, textvariable=self.sha256_result_var, 
                              wraplength=500, font=("Courier", 10), bg="white")
        result_label.pack(pady=10)

        frame_output.grid_columnconfigure(0, weight=1)

    def compute_sha256(self):
        input_text = self.sha256_input_var.get()
        if not input_text:
            messagebox.showwarning("Input Error", "Please enter some text!")
            return
        hashed = sha256(input_text)
        self.sha256_result_var.set(f"SHA-256 Hash:\n{hashed}")

    def clear_sha256_fields(self):
        self.sha256_input_var.set("")
        self.sha256_result_var.set("")

    # --------------------------- AES-CFB GUI HANDLING ---------------------------
    def load_aes_cfb_form(self):
        frame_main = tk.LabelFrame(self.main_frame, text="AES-CFB Cipher", padx=10, pady=10, bg="white")
        frame_main.pack(fill="both", expand=True)

        # Plaintext
        tk.Label(frame_main, text="Plaintext:", bg="white").grid(row=0, column=0, sticky='nw', padx=5, pady=5)
        self.txt_plain = scrolledtext.ScrolledText(frame_main, width=60, height=4)
        self.txt_plain.grid(row=0, column=1, padx=5, pady=5, sticky='ew')

        # Key
        tk.Label(frame_main, text="Key (16, 24, or 32 bytes):", bg="white").grid(row=1, column=0, sticky='w', padx=5, pady=5)
        self.entry_key = tk.Entry(frame_main, width=60)
        self.entry_key.grid(row=1, column=1, padx=5, pady=5, sticky='ew')

        # IV
        tk.Label(frame_main, text="IV (16 bytes):", bg="white").grid(row=2, column=0, sticky='w', padx=5, pady=5)
        self.entry_iv = tk.Entry(frame_main, width=60)
        self.entry_iv.grid(row=2, column=1, padx=5, pady=5, sticky='ew')

        # Buttons
        frame_buttons = tk.Frame(frame_main, bg="white")
        frame_buttons.grid(row=3, column=0, columnspan=2, pady=10)

        tk.Button(frame_buttons, text="Encrypt", command=self.aes_encrypt, 
                 bg="#4CAF50", fg="white").pack(side="left", padx=5)
        tk.Button(frame_buttons, text="Decrypt", command=self.aes_decrypt, 
                 bg="#f44336", fg="white").pack(side="left", padx=5)
        tk.Button(frame_buttons, text="Clear", command=self.clear_aes_fields).pack(side="left", padx=5)

        # Encrypted Text
        tk.Label(frame_main, text="Encrypted text (Base64):", bg="white").grid(row=4, column=0, sticky='nw', padx=5, pady=5)
        self.txt_cipher = scrolledtext.ScrolledText(frame_main, width=60, height=4)
        self.txt_cipher.grid(row=4, column=1, padx=5, pady=5, sticky='ew')

        # Decrypted Text
        tk.Label(frame_main, text="Decrypted text:", bg="white").grid(row=5, column=0, sticky='nw', padx=5, pady=5)
        self.txt_decrypted = scrolledtext.ScrolledText(frame_main, width=60, height=4)
        self.txt_decrypted.grid(row=5, column=1, padx=5, pady=5, sticky='ew')

        frame_main.grid_columnconfigure(1, weight=1)

    def validate_base64(self, text):
        pattern = r'^[A-Za-z0-9+/]*={0,2}$'
        return re.fullmatch(pattern, text) is not None

    def aes_encrypt(self):
        try:
            plaintext = self.txt_plain.get("1.0", tk.END).strip()
            if not plaintext:
                raise ValueError("Plaintext cannot be empty")
            
            key = self.entry_key.get().encode()
            iv = self.entry_iv.get().encode()
            
            if len(key) not in [16, 24, 32]:
                raise ValueError(f"Key must be 16, 24, or 32 bytes long (got {len(key)} bytes)")
            if len(iv) != 16:
                raise ValueError(f"IV must be exactly 16 bytes (got {len(iv)} bytes)")
            
            aes = AES_CFB(key, iv)
            ciphertext = aes.aesencrypt(plaintext.encode())
            
            b64_ct = b64encode(ciphertext).decode()
            self.txt_cipher.delete("1.0", tk.END)
            self.txt_cipher.insert(tk.END, b64_ct)
            
            # Clear decrypted text
            self.txt_decrypted.delete("1.0", tk.END)
            
        except Exception as e:
            messagebox.showerror("Encryption Error", str(e))
    
    def aes_decrypt(self):
        try:
            key = self.entry_key.get().encode()
            iv = self.entry_iv.get().encode()
            b64_ct = self.txt_cipher.get("1.0", tk.END).strip()
            
            if not b64_ct:
                raise ValueError("No ciphertext to decrypt")
            
            if not self.validate_base64(b64_ct):
                raise ValueError("Invalid Base64 format")
            
            ciphertext = b64decode(b64_ct)
            
            if len(key) not in [16, 24, 32]:
                raise ValueError(f"Key must be 16, 24, or 32 bytes long (got {len(key)} bytes)")
            if len(iv) != 16:
                raise ValueError(f"IV must be exactly 16 bytes (got {len(iv)} bytes)")
            
            aes = AES_CFB(key, iv)
            decrypted = aes.aesdecrypt(ciphertext)
            
            self.txt_decrypted.delete("1.0", tk.END)
            self.txt_decrypted.insert(tk.END, decrypted.decode(errors='replace'))
            
        except Exception as e:
            messagebox.showerror("Decryption Error", str(e))

    def clear_aes_fields(self):
        self.txt_plain.delete("1.0", tk.END)
        self.entry_key.delete(0, tk.END)
        self.entry_iv.delete(0, tk.END)
        self.txt_cipher.delete("1.0", tk.END)
        self.txt_decrypted.delete("1.0", tk.END)

    # --------------------------- DES GUI HANDLING ---------------------------
    def load_des_form(self):
        frame_main = tk.LabelFrame(self.main_frame, text="DES Cipher", padx=10, pady=10, bg="white")
        frame_main.pack(fill="both", expand=True)

        # Key
        tk.Label(frame_main, text="Key (8 chars):", bg="white").grid(row=0, column=0, sticky="e", padx=5, pady=5)
        self.des_key_entry = tk.Entry(frame_main, width=60)
        self.des_key_entry.grid(row=0, column=1, padx=5, pady=5, sticky="ew")

        # Text/Ciphertext
        tk.Label(frame_main, text="Text / Ciphertext:", bg="white").grid(row=1, column=0, sticky="ne", padx=5, pady=5)
        self.des_text_entry = scrolledtext.ScrolledText(frame_main, height=5, width=60)
        self.des_text_entry.grid(row=1, column=1, padx=5, pady=5, sticky="ew")

        # Mode selection
        self.des_mode_var = tk.StringVar(value="encrypt")
        frame_mode = tk.Frame(frame_main, bg="white")
        frame_mode.grid(row=2, column=0, columnspan=2, pady=5)
        tk.Radiobutton(frame_mode, text="Encrypt", variable=self.des_mode_var, 
                      value="encrypt", bg="white").pack(side="left", padx=5)
        tk.Radiobutton(frame_mode, text="Decrypt", variable=self.des_mode_var, 
                      value="decrypt", bg="white").pack(side="left", padx=5)

        # Button
        tk.Button(frame_main, text="Process", command=self.process_des, 
                 bg="#4CAF50", fg="white").grid(row=3, column=0, columnspan=2, pady=10)

        # Output
        tk.Label(frame_main, text="Output:", bg="white").grid(row=4, column=0, sticky="ne", padx=5, pady=5)
        self.des_output_text = scrolledtext.ScrolledText(frame_main, height=5, width=60)
        self.des_output_text.grid(row=4, column=1, padx=5, pady=5, sticky="ew")

        frame_main.grid_columnconfigure(1, weight=1)

    def process_des(self):
        key = self.des_key_entry.get()
        text = self.des_text_entry.get("1.0", tk.END).strip()
        try:
            if self.des_mode_var.get() == 'encrypt':
                result = des_encrypt(key, text)
            else:
                result = des_decrypt(key, text)
            self.des_output_text.delete("1.0", tk.END)
            self.des_output_text.insert(tk.END, result)
        except Exception as e:
            messagebox.showerror("Error", str(e))

# ============================== MAIN ====================================
if __name__ == "__main__":
    root = tk.Tk()
    app = EncryptionGUI(root)
    root.mainloop()