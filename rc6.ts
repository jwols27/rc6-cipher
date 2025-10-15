const WORD_SIZE = 32;
const LOG_WORD_SIZE = 5;
const NUM_ROUNDS = 20;
const P32 = 0xB7E15163 >>> 0;
const Q32 = 0x9E3779B9 >>> 0;
const BLOCK_SIZE = 16;

function rotateLeft32(value: number, shift: number): number {
    shift &= 31;
    return ((value << shift) | (value >>> (32 - shift))) >>> 0;
}

function rotateRight32(value: number, shift: number): number {
    shift &= 31;
    return ((value >>> shift) | (value << (32 - shift))) >>> 0;
}

// little-endian
function readUInt32LE(bytes: Uint8Array, offset: number): number {
    return (
        (bytes[offset]) |
        (bytes[offset + 1] << 8) |
        (bytes[offset + 2] << 16) |
        (bytes[offset + 3] << 24)
    ) >>> 0;
}

// little-endian
function writeUInt32LE(buffer: Uint8Array, offset: number, value: number): void {
    buffer[offset] = value & 0xff;
    buffer[offset + 1] = (value >>> 8) & 0xff;
    buffer[offset + 2] = (value >>> 16) & 0xff;
    buffer[offset + 3] = (value >>> 24) & 0xff;
}

function expandKey(): number[] {
    const secretKey = getKeyBytes();
    const keyLength = secretKey.length;
    const numWords = Math.max(1, Math.ceil(keyLength / 4));
    const L = new Array(numWords).fill(0);

    for (let i = keyLength - 1; i >= 0; i--) {
        const wordIndex = Math.floor(i / 4);
        L[wordIndex] = ((L[wordIndex] << 8) + secretKey[i]) >>> 0;
    }

    const t = 2 * NUM_ROUNDS + 4;
    const S = new Array(t);
    S[0] = P32;
    for (let i = 1; i < t; i++) {
        S[i] = (S[i - 1] + Q32) >>> 0;
    }

    let A = 0, B = 0, i = 0, j = 0;
    const iterations = 3 * Math.max(numWords, t);
    for (let k = 0; k < iterations; k++) {
        A = S[i] = rotateLeft32((S[i] + A + B) >>> 0, 3);
        B = L[j] = rotateLeft32((L[j] + A + B) >>> 0, (A + B) >>> 0);
        i = (i + 1) % t;
        j = (j + 1) % numWords;
    }

    return S;
}

function encryptBlockRC6(plainBlock: Uint8Array, expandedKey: number[]): Uint8Array {
    let A = readUInt32LE(plainBlock, 0);
    let B = readUInt32LE(plainBlock, 4);
    let C = readUInt32LE(plainBlock, 8);
    let D = readUInt32LE(plainBlock, 12);

    B = (B + expandedKey[0]) >>> 0;
    D = (D + expandedKey[1]) >>> 0;

    for (let i = 1; i <= NUM_ROUNDS; i++) {
        const t = rotateLeft32(Math.imul(B, ((B << 1) + 1) >>> 0) >>> 0, LOG_WORD_SIZE);
        const u = rotateLeft32(Math.imul(D, ((D << 1) + 1) >>> 0) >>> 0, LOG_WORD_SIZE);
        const tmod = t & 31, umod = u & 31;

        A = (rotateLeft32((A ^ t) >>> 0, umod) + expandedKey[2 * i]) >>> 0;
        C = (rotateLeft32((C ^ u) >>> 0, tmod) + expandedKey[2 * i + 1]) >>> 0;
        [A, B, C, D] = [B, C, D, A];
    }

    A = (A + expandedKey[2 * NUM_ROUNDS + 2]) >>> 0;
    C = (C + expandedKey[2 * NUM_ROUNDS + 3]) >>> 0;

    const output = new Uint8Array(16);
    writeUInt32LE(output, 0, A);
    writeUInt32LE(output, 4, B);
    writeUInt32LE(output, 8, C);
    writeUInt32LE(output, 12, D);
    return output;
}

function decryptBlockRC6(cipherBlock: Uint8Array, expandedKey: number[]): Uint8Array {
    let A = readUInt32LE(cipherBlock, 0);
    let B = readUInt32LE(cipherBlock, 4);
    let C = readUInt32LE(cipherBlock, 8);
    let D = readUInt32LE(cipherBlock, 12);

    C = (C - expandedKey[2 * NUM_ROUNDS + 3]) >>> 0;
    A = (A - expandedKey[2 * NUM_ROUNDS + 2]) >>> 0;

    for (let i = NUM_ROUNDS; i >= 1; i--) {
        [A, B, C, D] = [D, A, B, C];
        const t = rotateLeft32(Math.imul(B, ((B << 1) + 1) >>> 0) >>> 0, LOG_WORD_SIZE);
        const u = rotateLeft32(Math.imul(D, ((D << 1) + 1) >>> 0) >>> 0, LOG_WORD_SIZE);
        const tmod = t & 31, umod = u & 31;

        C = rotateRight32((C - expandedKey[2 * i + 1]) >>> 0, tmod) ^ u;
        A = rotateRight32((A - expandedKey[2 * i]) >>> 0, umod) ^ t;
    }

    D = (D - expandedKey[1]) >>> 0;
    B = (B - expandedKey[0]) >>> 0;

    const output = new Uint8Array(16);
    writeUInt32LE(output, 0, A);
    writeUInt32LE(output, 4, B);
    writeUInt32LE(output, 8, C);
    writeUInt32LE(output, 12, D);
    return output;
}

// PKCS7
function pad(data: Uint8Array): Uint8Array {
    const paddingLength = BLOCK_SIZE - (data.length % BLOCK_SIZE || BLOCK_SIZE);
    const padded = new Uint8Array(data.length + paddingLength);
    padded.set(data);
    padded.fill(paddingLength, data.length);
    return padded;
}

// PKCS7
function unpad(data: Uint8Array): Uint8Array {
    const padLen = data[data.length - 1];
    if (padLen <= 0 || padLen > BLOCK_SIZE) throw new Error("Inválido");
    return data.subarray(0, data.length - padLen);
}

function bytesToHex(data: Uint8Array): string {
    return Array.from(data).map(b => b.toString(16).padStart(2, "0")).join("");
}

function hexToBytes(hex: string): Uint8Array {
    hex = hex.replace(/\s+/g, "");
    if (hex.length % 2) hex = "0" + hex;
    const out = new Uint8Array(hex.length / 2);
    for (let i = 0; i < out.length; i++) out[i] = parseInt(hex.substr(i * 2, 2), 16);
    return out;
}

function encrypt(plainData: Uint8Array, expandedKey: number[]): Uint8Array {
    const output = new Uint8Array(plainData.length);
    for (let i = 0; i < plainData.length; i += BLOCK_SIZE) {
        const block = plainData.subarray(i, i + BLOCK_SIZE);
        output.set(encryptBlockRC6(block, expandedKey), i);
    }
    return output;
}

function decrypt(cipherData: Uint8Array, expandedKey: number[]): Uint8Array {
    const output = new Uint8Array(cipherData.length);
    for (let i = 0; i < cipherData.length; i += BLOCK_SIZE) {
        const block = cipherData.subarray(i, i + BLOCK_SIZE);
        output.set(decryptBlockRC6(block, expandedKey), i);
    }
    return output;
}

function getKeyBytes(key: string = ""): Uint8Array {
    if (!key) {
        key = (document.getElementById("key") as HTMLInputElement).value;
    }
    return new TextEncoder().encode(key.padEnd(16, "\0").slice(0, 16));
}

let lastCipherHex = "";

function encryptMessage() {
    const msg = (document.getElementById("message") as HTMLTextAreaElement).value;
    const msgBytes = new TextEncoder().encode(msg);
    const S = expandKey();
    const cipher = encrypt(pad(msgBytes), S);
    lastCipherHex = bytesToHex(cipher);
    (document.getElementById("cipher") as HTMLElement).textContent = lastCipherHex.match(/.{1,32}/g)?.join("\n") ?? "";
    (document.getElementById("plain") as HTMLElement).textContent = "";
    (document.getElementById("cipher-input") as HTMLTextAreaElement).value = lastCipherHex;
};

document.getElementById("encrypt-button")?.addEventListener("click", encryptMessage);

function decryptMessage() {
    if (!lastCipherHex) { alert("Criptografe primeiro."); return; }
    try {
        const S = expandKey();
        const plainBytes = unpad(decrypt(hexToBytes(lastCipherHex), S));
        const element = document.getElementById("plain");
        if (!element) return;
        element.textContent = new TextDecoder().decode(plainBytes);
    } catch (e) {
        alert("Erro ao descriptografar: " + (e as Error).message);
    }
};

document.getElementById("decrypt-button")?.addEventListener("click", decryptMessage);

function decryptHexInput() {
    const hexInput = (document.getElementById("cipher-input") as HTMLTextAreaElement).value.trim();
    if (!hexInput) { return; }
    try {
        const bytes = hexToBytes(hexInput);
        if (bytes.length % BLOCK_SIZE !== 0) { alert("Texto criptografado deve corresponder a um múltiplo de 16."); return; }
        const S = expandKey();
        const plainBytes = unpad(decrypt(bytes, S));
        const element = document.getElementById("plain");
        if (!element) return;
        element.textContent = new TextDecoder().decode(plainBytes);
        lastCipherHex = bytesToHex(bytes);
    } catch (e) {
        alert("Erro ao descriptografar: " + (e as Error).message);
    }
};

document.getElementById("manual-decrypt-button")?.addEventListener("click", decryptHexInput);

function updateKeyHex(event?: Event) {
    const target = event?.target as HTMLInputElement | undefined;
    const keyBytes = getKeyBytes(target?.value);
    const hex = Array.from(keyBytes).map(x => x.toString(16).padStart(2, "0")).join(" ");
    const element = document.getElementById("key-hex");
    if (!element) return;
    element.textContent = hex;
}

document.getElementById("key")?.addEventListener("input", (event) => updateKeyHex(event))

updateKeyHex();
