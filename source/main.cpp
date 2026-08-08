#include <3ds.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <dirent.h>
#include <sys/stat.h>
#include <sys/statvfs.h>
#include <errno.h>
#include <setjmp.h>
#include <cctype>
#include <vector>
#include <string>
#include <map>

extern "C" {
#include <jpeglib.h>
#include <jerror.h>
}

// ==================== CONFIG ====================
static const char* SRC_DIR        = "sdmc:/luma/screenshots/";
static const char* DCIM_BASE      = "sdmc:/DCIM/";
static const int   JPEG_QUALITY   = 90;
static const int   MAX_FILES_PER_DIR = 999;

static int g_dirIdx  = 100;
static int g_fileIdx = 1;

PrintConsole topScreen, bottomScreen;

// ==================== EXIF TEMPLATE & TIMESTAMP ====================
static unsigned char exif_template_prefix[] = {
    // --- APP1 Header ---
    0x45, 0x78, 0x69, 0x66, 0x00, 0x00,             // "Exif\0\0" identifier

    // --- TIFF Header (Offsets start here: Index 6 = 0x00) ---
    0x4D, 0x4D, 0x00, 0x2A, 0x00, 0x00, 0x00, 0x08, // Big-endian, Magic 42, IFD0 at offset 8

    // --- IFD0: 6 entries (Sorted by tag number) ---
    0x00, 0x06,                                     // Number of directory entries
    // 0x010F Make      (ASCII, 10 bytes incl. padding)
    0x01, 0x0F, 0x00, 0x02, 0x00, 0x00, 0x00, 0x0A, 0x00, 0x00, 0x00, 0x56,
    // 0x0110 Model     (ASCII, 14 bytes incl. padding)
    0x01, 0x10, 0x00, 0x02, 0x00, 0x00, 0x00, 0x0E, 0x00, 0x00, 0x00, 0x60,
    // 0x0131 Software  (ASCII, 6 bytes)
    0x01, 0x31, 0x00, 0x02, 0x00, 0x00, 0x00, 0x06, 0x00, 0x00, 0x00, 0x6E,
    // 0x0132 DateTime  (ASCII, 20 bytes)
    0x01, 0x32, 0x00, 0x02, 0x00, 0x00, 0x00, 0x14, 0x00, 0x00, 0x00, 0x74,
    // 0x013B Artist    (ASCII, 16 bytes)
    0x01, 0x3B, 0x00, 0x02, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x88,
    // 0x8769 ExifIFD   (LONG, 1 value pointing to Sub-IFD)
    0x87, 0x69, 0x00, 0x04, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x98,

    0x00, 0x00, 0x00, 0x00,                         // Next IFD offset (none)

    // --- DATA SECTION (Offsets relative to TIFF Header at Index 6) ---
    'N','i','n','t','e','n','d','o',0x00, 0x00,
    'N','i','n','t','e','n','d','o',' ','3','D','S',0x00, 0x00,
    '0','0','2','2','7',0x00,
    '2','0','0','1',':','0','1',':','0','1',' ','0','0',':','0','0',':','0','0',0x00,
    'S','C','R','2','J','P','G',' ','f','o','r',' ','3','D','S',0x00,
};

static const int EXIF_DATETIME_OFFSET = 122;

static bool endsWith(const std::string& s, const std::string& suffix) {
    return s.size() >= suffix.size() &&
           s.compare(s.size() - suffix.size(), suffix.size(), suffix) == 0;
}

static int getOffsetSecondsForFilename(const std::string& fname) {
    if (endsWith(fname, "_top.bmp")) return 1;
    if (endsWith(fname, "_top_right.bmp")) return 2;
    return 0;
}

// Splits "2024-01-01_12-00-00.000_top.bmp" into prefix="2024-01-01_12-00-00.000"
// and suffix="_top.bmp". Used to find files that belong to the same shot
// (same timestamp) so _top/_top_right pairs can be combined into one MPO.
// Returns false if fname doesn't match the expected Luma3DS timestamp pattern.
static bool getFilePrefixAndSuffix(const std::string& fname, std::string& prefix, std::string& suffix) {
    if (fname.size() < 22 || fname[4] != '-' || fname[7] != '-' || fname[10] != '_' ||
        fname[13] != '-' || fname[16] != '-' || fname[19] != '.') {
        return false;
    }
    size_t nextUnderscore = fname.find('_', 20);
    if (nextUnderscore == std::string::npos || nextUnderscore <= 20) return false;
    prefix = fname.substr(0, nextUnderscore);
    suffix = fname.substr(nextUnderscore);
    return true;
}

static void parseTimestampFromFilename(const std::string& filepath, int offsetSeconds, char out[20]) {
    static const char FALLBACK[20] = "2001:01:01 00:00:00";

    std::string fname;
    size_t slash = filepath.find_last_of('/');
    fname = (slash != std::string::npos) ? filepath.substr(slash + 1) : filepath;

    if (fname.size() < 22 || fname[4] != '-' || fname[7] != '-' || fname[10] != '_' ||
        fname[13] != '-' || fname[16] != '-' || fname[19] != '.') {
        memcpy(out, FALLBACK, 20);
        return;
    }

    int Y = 0, Mo = 0, D = 0, H = 0, Mi = 0, S = 0;
    if (sscanf(fname.c_str(), "%4d-%2d-%2d_%2d-%2d-%2d", &Y, &Mo, &D, &H, &Mi, &S) != 6) {
        memcpy(out, FALLBACK, 20);
        return;
    }

    if (Y < 2000 || Y > 2099 || Mo < 1 || Mo > 12 || D < 1 || D > 31 ||
        H < 0 || H > 23 || Mi < 0 || Mi > 59 || S < 0 || S > 59) {
        memcpy(out, FALLBACK, 20);
        return;
    }

    size_t nextUnderscore = fname.find('_', 20);
    if (nextUnderscore == std::string::npos || nextUnderscore <= 20) {
        memcpy(out, FALLBACK, 20);
        return;
    }

    S  += offsetSeconds;
    Mi += S  / 60;  S  %= 60;
    H  += Mi / 60;  Mi %= 60;
    D  += H  / 24;  H  %= 24;

    snprintf(out, 20, "%04d:%02d:%02d %02d:%02d:%02d", Y, Mo, D, H, Mi, S);
}

static void appendU16(std::vector<unsigned char>& v, uint16_t x) {
    v.push_back((unsigned char)((x >> 8) & 0xFF));
    v.push_back((unsigned char)(x & 0xFF));
}
static void appendU32(std::vector<unsigned char>& v, uint32_t x) {
    v.push_back((unsigned char)((x >> 24) & 0xFF));
    v.push_back((unsigned char)((x >> 16) & 0xFF));
    v.push_back((unsigned char)((x >> 8)  & 0xFF));
    v.push_back((unsigned char)(x & 0xFF));
}

static void addNintendoExif(jpeg_compress_struct* cinfo, const char datetime[20], int entryNumber) {
    std::vector<unsigned char> buf(exif_template_prefix, exif_template_prefix + sizeof(exif_template_prefix));
    memcpy(buf.data() + EXIF_DATETIME_OFFSET, datetime, 20);

    char numStr[16];
    snprintf(numStr, sizeof(numStr), "%d", entryNumber);
    size_t numLen = strlen(numStr);
    static const unsigned char ASCII_CODE[8] = { 'A','S','C','I','I', 0x00, 0x00, 0x00 };

    const size_t SUBIFD_TIFF_OFFSET        = 0x98;
    const size_t SUBIFD_HEADER_SIZE        = 2 + 3 * 12 + 4;
    const size_t DATETIME_ORIG_TIFF_OFFSET = SUBIFD_TIFF_OFFSET + SUBIFD_HEADER_SIZE;
    const size_t USERCOMMENT_TIFF_OFFSET   = DATETIME_ORIG_TIFF_OFFSET + 20;

    appendU16(buf, 0x0003);

    appendU16(buf, 0x9000); appendU16(buf, 7); appendU32(buf, 4);
    buf.push_back('0'); buf.push_back('2'); buf.push_back('2'); buf.push_back('0');

    appendU16(buf, 0x9003); appendU16(buf, 2); appendU32(buf, 20);
    appendU32(buf, (uint32_t)DATETIME_ORIG_TIFF_OFFSET);

    appendU16(buf, 0x9286); appendU16(buf, 7); appendU32(buf, (uint32_t)(8 + numLen));
    appendU32(buf, (uint32_t)USERCOMMENT_TIFF_OFFSET);

    appendU32(buf, 0);

    buf.insert(buf.end(), datetime, datetime + 20);
    buf.insert(buf.end(), ASCII_CODE, ASCII_CODE + 8);
    buf.insert(buf.end(), numStr, numStr + numLen);

    jpeg_write_marker(cinfo, 0xE1, buf.data(), (unsigned int)buf.size());
}

// ==================== HELPERS ====================
typedef struct { struct jpeg_error_mgr pub; jmp_buf setjmp_buffer; } *my_error_ptr;
void my_error_exit(j_common_ptr cinfo) { longjmp(((my_error_ptr)cinfo->err)->setjmp_buffer, 1); }

#pragma pack(push, 1)
struct BmpHeader {
    uint16_t sig; uint32_t size; uint16_t r1, r2; uint32_t offset;
    uint32_t hSize; int32_t w, h; uint16_t planes, bpp; uint32_t comp;
};
#pragma pack(pop)

bool isBmp(const std::string& f) {
    if (f.length() < 4) return false;
    std::string ext = f.substr(f.length() - 4);
    for (auto& c : ext) c = tolower(c);
    return ext == ".bmp";
}

bool hasEnoughSpace() {
    struct statvfs fiData;
    if (statvfs("sdmc:/", &fiData) < 0) return true;
    uint64_t freeBytes = (uint64_t)fiData.f_bavail * (uint64_t)fiData.f_frsize;
    return freeBytes > (1024 * 1024);
}

static bool getNextOutputPath(char* outPath, size_t size, const char* ext) {
    const char* altExt = (strcmp(ext, "JPG") == 0) ? "MPO" : "JPG";
    for (; g_dirIdx <= 999; g_dirIdx++, g_fileIdx = 1) {
        char dirPath[256];
        snprintf(dirPath, sizeof(dirPath), "%s%03dNIN03", DCIM_BASE, g_dirIdx);
        if (mkdir(dirPath, 0777) != 0 && errno != EEXIST) {
            // Verzeichnis konnte nicht angelegt werden (SD voll, Rechte, ...) ->
            // diesen Ordner ueberspringen statt spaeter mit einem generischen
            // fopen()-Fehlschlag zu enden.
            continue;
        }
        for (; g_fileIdx <= MAX_FILES_PER_DIR; g_fileIdx++) {
            snprintf(outPath, size, "%s/HNI_%04d.%s", dirPath, g_fileIdx, ext);
            char altPath[256];
            snprintf(altPath, sizeof(altPath), "%s/HNI_%04d.%s", dirPath, g_fileIdx, altExt);
            struct stat st;
            // Sowohl die eigene als auch die jeweils andere Endung pruefen:
            // HNI_XXXX.JPG und HNI_XXXX.MPO teilen sich denselben Nummernraum
            // (wie bei der echten 3DS-Kamera) und duerfen nicht kollidieren.
            if (stat(outPath, &st) != 0 && stat(altPath, &st) != 0) {
                g_fileIdx++;
                return true;
            }
        }
    }
    return false;
}

static std::vector<uint8_t> loadBmp(const char* path, int& w, int& h) {
    FILE* f = fopen(path, "rb");
    if (!f) return {};
    BmpHeader hdr;
    if (fread(&hdr, sizeof(hdr), 1, f) != 1 || hdr.sig != 0x4D42) { fclose(f); return {}; }
    w = hdr.w; h = abs(hdr.h);
    // Plausibilitaetscheck: negative/0/absurd grosse Werte (kaputter oder
    // manipulierter Header) statt Crash bei der Vektor-Allokation abfangen.
    if (w <= 0 || h <= 0 || w > 4096 || h > 4096) { fclose(f); return {}; }
    int srcBpp = hdr.bpp / 8;
    if (hdr.comp != 0 || (srcBpp != 3 && srcBpp != 4)) { fclose(f); return {}; }
    int rowStride = ((w * srcBpp) + 3) & ~3;
    std::vector<uint8_t> rgb(w * h * 3);
    std::vector<uint8_t> rowBuf(rowStride);
    fseek(f, hdr.offset, SEEK_SET);
    for (int y = 0; y < h; y++) {
        if (fread(rowBuf.data(), 1, rowStride, f) != (size_t)rowStride) {
            // Abgeschnittene/kaputte BMP: NICHT den halb befuellten Buffer
            // zurueckgeben (der Aufrufer wuerde das faelschlich als Erfolg
            // werten und ein korruptes Foto als [OK] nach DCIM schreiben).
            fclose(f);
            return {};
        }
        int targetY = (hdr.h > 0) ? (h - 1 - y) : y;
        uint8_t* dst = &rgb[targetY * w * 3];
        for (int x = 0; x < w; x++) {
            dst[x * 3 + 0] = rowBuf[x * srcBpp + 2];
            dst[x * 3 + 1] = rowBuf[x * srcBpp + 1];
            dst[x * 3 + 2] = rowBuf[x * srcBpp + 0];
        }
    }
    fclose(f);
    return rgb;
}

// Komprimiert RGB-Bilddaten zu einem JPEG-Bytestrom im Speicher (kein Datei-I/O).
// extraMarkerPayload (falls != nullptr) wird als zusätzlicher APP2-Marker direkt
// nach dem Nintendo-EXIF (APP1) geschrieben - genau dort erwartet der CIPA
// MPF-Standard das APP2 "MPF"-Segment (siehe MPO-Abschnitt weiter unten).
static bool compressJpeg(const std::vector<uint8_t>& rgb, int w, int h,
                          const char datetime[20], int entryNumber,
                          const std::vector<unsigned char>* extraMarkerPayload,
                          std::vector<unsigned char>& outBuf) {
    struct jpeg_compress_struct cinfo;
    struct { struct jpeg_error_mgr pub; jmp_buf setjmp_buffer; } jerr;
    cinfo.err = jpeg_std_error(&jerr.pub);
    jerr.pub.error_exit = my_error_exit;

    unsigned char* mem_buf = nullptr;
    unsigned long  mem_size = 0;

    if (setjmp(jerr.setjmp_buffer)) {
        jpeg_destroy_compress(&cinfo);
        free(mem_buf);
        return false;
    }

    jpeg_create_compress(&cinfo);
    jpeg_mem_dest(&cinfo, &mem_buf, &mem_size);
    cinfo.image_width      = w;
    cinfo.image_height     = h;
    cinfo.input_components = 3;
    cinfo.in_color_space   = JCS_RGB;
    jpeg_set_defaults(&cinfo);
    jpeg_set_quality(&cinfo, JPEG_QUALITY, TRUE);
    jpeg_start_compress(&cinfo, TRUE);
    addNintendoExif(&cinfo, datetime, entryNumber);
    if (extraMarkerPayload) {
        jpeg_write_marker(&cinfo, 0xE2, extraMarkerPayload->data(), (unsigned int)extraMarkerPayload->size());
    }
    while (cinfo.next_scanline < cinfo.image_height) {
        JSAMPROW row = (JSAMPROW)&rgb[cinfo.next_scanline * w * 3];
        jpeg_write_scanlines(&cinfo, &row, 1);
    }
    jpeg_finish_compress(&cinfo);
    jpeg_destroy_compress(&cinfo);

    outBuf.assign(mem_buf, mem_buf + mem_size);
    free(mem_buf);
    return true;
}

static bool saveJpeg(const char* path, const std::vector<uint8_t>& rgb, int w, int h,
                     const char datetime[20], int entryNumber) {
    std::vector<unsigned char> buf;
    if (!compressJpeg(rgb, w, h, datetime, entryNumber, nullptr, buf)) return false;

    FILE* f = fopen(path, "wb");
    if (!f) return false;
    bool ok = (fwrite(buf.data(), 1, buf.size(), f) == buf.size());
    fclose(f);
    return ok;
}

// ==================== MPO (3D-Fotos) ====================
// Nintendo speichert 3D-Fotos im MPO-Format (CIPA "Multi Picture Format",
// DC-007). Eine MPO-Datei ist einfach zwei vollständige JPEGs (SOI...EOI)
// hintereinander in einer Datei. Das erste (linke/_top) Bild bekommt einen
// zusätzlichen APP2-Marker mit dem "MP Index IFD" (Größe/Position beider
// Bilder); das zweite (rechte/_top_right) Bild bekommt einen kleineren,
// statischen APP2-Marker mit seinen eigenen MP-Attributen. Beide APP2-Marker
// müssen direkt hinter dem jeweiligen EXIF-APP1 stehen. Das Byte-Layout
// wurde gegen eine bekannte 3DS-kompatible Referenzimplementierung
// (labocho/makempo) verifiziert.

static void appendAscii(std::vector<unsigned char>& v, const char* s, size_t n) {
    for (size_t i = 0; i < n; i++) v.push_back((unsigned char)s[i]);
}

// Baut den APP2-"MPF"-Payload für das ERSTE Bild (enthält den MP Index).
// Drei Felder sind erst nach dem Komprimieren bekannt (Größe von Bild 1,
// Größe von Bild 2, Offset zu Bild 2) und werden hier als Platzhalter (0)
// geschrieben; ihre Positionen im Payload werden über die Ausgabeparameter
// zurückgegeben, damit saveMpo() sie später patchen kann.
static std::vector<unsigned char> buildMpIndexApp2Payload(size_t& size1Pos,
                                                            size_t& size2Pos,
                                                            size_t& offset2Pos) {
    std::vector<unsigned char> p;
    appendAscii(p, "MPF", 3); p.push_back(0x00);       // MPF-Identifier -> ab hier beginnt die MPF-Base (Offset 0)
    p.push_back(0x4D); p.push_back(0x4D); p.push_back(0x00); p.push_back(0x2A); // TIFF-Header, Big-Endian, Magic 42
    appendU32(p, 8);                                    // Offset zum ersten IFD (relativ zur MPF-Base)

    // ---- MP Index IFD (nur im ersten Bild vorhanden) ----
    appendU16(p, 3);                                    // 3 Einträge

    // 0xB000 MPFVersion (UNDEFINED, count 4, "0100" passt inline in die 4 Bytes)
    appendU16(p, 0xB000); appendU16(p, 0x0007); appendU32(p, 4);
    appendAscii(p, "0100", 4);

    // 0xB001 NumberOfImages (LONG, count 1, Wert 2)
    appendU16(p, 0xB001); appendU16(p, 0x0004); appendU32(p, 1);
    appendU32(p, 2);

    // 0xB002 MPEntry (UNDEFINED, count 32 = 2*16 Bytes, Offset 0x32 zur MP-Entry-Liste)
    appendU16(p, 0xB002); appendU16(p, 0x0007); appendU32(p, 32);
    appendU32(p, 0x32);

    appendU32(p, 0x52);                                 // Offset zum nächsten IFD (MP Attributes IFD)

    // ---- MP-Entry-Array (2 * 16 Bytes) @ MPF-Base-relativ 0x32 ----
    // Eintrag 1: primäres/repräsentatives Bild (top, links)
    appendU32(p, 0x20020002);                           // Flags: repräsentativ | Format: JPEG | Typ: Multi-frame Disparity
    size1Pos = p.size();
    appendU32(p, 0);                                    // PLATZHALTER: Größe Bild 1 (SOI..EOI)
    appendU32(p, 0);                                    // Datenoffset Bild 1 = 0 (liegt vor der eigenen MPF-Base)
    appendU16(p, 0); appendU16(p, 0);                    // Dependent-Entry-Nummern

    // Eintrag 2: rechtes Bild (top_right)
    appendU32(p, 0x00020002);                           // Flags: keine | Format: JPEG | Typ: Multi-frame Disparity
    size2Pos = p.size();
    appendU32(p, 0);                                    // PLATZHALTER: Größe Bild 2 (SOI..EOI)
    offset2Pos = p.size();
    appendU32(p, 0);                                    // PLATZHALTER: Offset zur SOI von Bild 2 (relativ zur MPF-Base)
    appendU16(p, 0); appendU16(p, 0);

    // ---- MP Attributes IFD für Bild 1 selbst @ MPF-Base-relativ 0x52 ----
    appendU16(p, 4);
    appendU16(p, 0xB101); appendU16(p, 0x0004); appendU32(p, 1); appendU32(p, 1);    // eigene Bildnummer = 1
    appendU16(p, 0xB204); appendU16(p, 0x0004); appendU32(p, 1); appendU32(p, 1);    // BaseViewpointNumber = 1
    appendU16(p, 0xB205); appendU16(p, 0x000A); appendU32(p, 1); appendU32(p, 0x88); // ConvergenceAngle -> Offset 0x88
    appendU16(p, 0xB206); appendU16(p, 0x0005); appendU32(p, 1); appendU32(p, 0x90); // BaselineLength   -> Offset 0x90
    appendU32(p, 0);                                     // Offset nächstes IFD = keins
    appendU32(p, 0xFFFFFFFF); appendU32(p, 0xFFFFFFFF);  // ConvergenceAngle: nicht angegeben
    appendU32(p, 0xFFFFFFFF); appendU32(p, 0xFFFFFFFF);  // BaselineLength:   nicht angegeben

    return p;
}

// Baut den (statischen) APP2-"MPF"-Payload für das ZWEITE Bild. Enthält keine
// erst-nach-dem-Komprimieren bekannten Werte und muss daher nicht gepatcht werden.
static std::vector<unsigned char> buildIndividualApp2Payload() {
    std::vector<unsigned char> p;
    appendAscii(p, "MPF", 3); p.push_back(0x00);
    p.push_back(0x4D); p.push_back(0x4D); p.push_back(0x00); p.push_back(0x2A);
    appendU32(p, 8);

    appendU16(p, 5);
    appendU16(p, 0xB000); appendU16(p, 0x0007); appendU32(p, 4);
    appendAscii(p, "0100", 4);
    appendU16(p, 0xB101); appendU16(p, 0x0004); appendU32(p, 1); appendU32(p, 2);    // eigene Bildnummer = 2
    appendU16(p, 0xB204); appendU16(p, 0x0004); appendU32(p, 1); appendU32(p, 1);
    appendU16(p, 0xB205); appendU16(p, 0x000A); appendU32(p, 1); appendU32(p, 0x4A);
    appendU16(p, 0xB206); appendU16(p, 0x0005); appendU32(p, 1); appendU32(p, 0x52);
    appendU32(p, 0);
    appendU32(p, 0xFFFFFFFF); appendU32(p, 0xFFFFFFFF);
    appendU32(p, 0xFFFFFFFF); appendU32(p, 0xFFFFFFFF);

    return p;
}

static void patchU32BE(std::vector<unsigned char>& buf, size_t pos, uint32_t val) {
    buf[pos + 0] = (unsigned char)((val >> 24) & 0xFF);
    buf[pos + 1] = (unsigned char)((val >> 16) & 0xFF);
    buf[pos + 2] = (unsigned char)((val >> 8)  & 0xFF);
    buf[pos + 3] = (unsigned char)(val & 0xFF);
}

// Sucht den APP2 "MPF\0"-Marker in einem komprimierten JPEG-Buffer und gibt
// die Position von "MPF\0" selbst zurück (== Payload-Anfang, == MPF-Base - 4).
// Gibt (size_t)-1 zurück, falls nicht gefunden.
static size_t findMpfPayloadStart(const std::vector<unsigned char>& buf) {
    if (buf.size() < 8) return (size_t)-1;
    for (size_t i = 0; i + 8 <= buf.size(); i++) {
        if (buf[i] == 0xFF && buf[i + 1] == 0xE2 &&
            buf[i + 4] == 'M' && buf[i + 5] == 'P' && buf[i + 6] == 'F' && buf[i + 7] == 0x00) {
            return i + 4;
        }
    }
    return (size_t)-1;
}

// Wandelt ein _top.bmp + _top_right.bmp Paar in eine einzelne MPO-Datei um
// (3D-Foto, wie es die Nintendo-3DS-Kamera erzeugt). Beide Bilder teilen sich
// dieselbe entryNumber, da sie logisch ein einziges Foto sind.
static bool saveMpo(const char* path,
                     const std::vector<uint8_t>& rgbTop, int wTop, int hTop, const char datetimeTop[20],
                     const std::vector<uint8_t>& rgbRight, int wRight, int hRight, const char datetimeRight[20],
                     int entryNumber) {
    if (wTop != wRight || hTop != hRight) return false; // bei einem echten Paar sollte das nie auftreten

    size_t size1Pos = 0, size2Pos = 0, offset2Pos = 0;
    std::vector<unsigned char> payload1 = buildMpIndexApp2Payload(size1Pos, size2Pos, offset2Pos);
    std::vector<unsigned char> payload2 = buildIndividualApp2Payload();

    std::vector<unsigned char> buf1, buf2;
    if (!compressJpeg(rgbTop,   wTop,   hTop,   datetimeTop,   entryNumber, &payload1, buf1)) return false;
    if (!compressJpeg(rgbRight, wRight, hRight, datetimeRight, entryNumber, &payload2, buf2)) return false;

    size_t payloadStart = findMpfPayloadStart(buf1);
    if (payloadStart == (size_t)-1) return false; // sollte nie passieren, defensive Absicherung

    uint32_t size1   = (uint32_t)buf1.size();
    uint32_t size2   = (uint32_t)buf2.size();
    uint32_t mpfBase = (uint32_t)(payloadStart + 4);  // 4 = Länge von "MPF\0"
    uint32_t offset2 = size1 - mpfBase;                // Bild 2 folgt direkt nach Bild 1

    patchU32BE(buf1, payloadStart + size1Pos,   size1);
    patchU32BE(buf1, payloadStart + size2Pos,   size2);
    patchU32BE(buf1, payloadStart + offset2Pos, offset2);

    FILE* f = fopen(path, "wb");
    if (!f) return false;
    bool ok = (fwrite(buf1.data(), 1, buf1.size(), f) == buf1.size()) &&
              (fwrite(buf2.data(), 1, buf2.size(), f) == buf2.size());
    fclose(f);
    return ok;
}

// ==================== TXT-VERWALTUNGSSYSTEM ====================
static const char* TXT_LOG_PATH = "sdmc:/DCIM/SCR2JPG.txt";

struct LogEntry {
    int number = 0;
    std::string jpgPath;
    bool locked = false;

    LogEntry() : number(0), locked(false) {}
    LogEntry(int num, const std::string& path, bool lk)
    : number(num), jpgPath(path), locked(lk) {}
};

static std::map<std::string, LogEntry> g_logIndex;
static int g_nextEntryNumber = 1;

static std::string shortenJpgPath(const std::string& fullPath) {
    size_t lastSlash = fullPath.find_last_of('/');
    if (lastSlash == std::string::npos) return fullPath;
    size_t secondLastSlash = fullPath.find_last_of('/', lastSlash - 1);
    if (secondLastSlash == std::string::npos) return fullPath;
    return fullPath.substr(secondLastSlash + 1);
}

static bool parseLogLine(const std::string& line, int& outNum, std::string& outBmp,
                          std::string& outJpg, bool& outLocked) {
    size_t dashPos = line.find(" - ");
    if (dashPos == std::string::npos) return false;

    std::string numPart = line.substr(0, dashPos);
    if (numPart.empty()) return false;
    for (char c : numPart) if (!isdigit((unsigned char)c)) return false;

    size_t arrowPos = line.find(" >> ", dashPos + 3);
    if (arrowPos == std::string::npos) return false;
    std::string bmp = line.substr(dashPos + 3, arrowPos - (dashPos + 3));
    if (bmp.empty()) return false;

    std::string rest = line.substr(arrowPos + 4);
    bool locked = false;
    if (rest.size() >= 2 && rest.compare(rest.size() - 2, 2, " X") == 0) {
        locked = true;
        rest = rest.substr(0, rest.size() - 2);
    }
    if (rest.empty()) return false;

    outNum    = atoi(numPart.c_str());
    outBmp    = bmp;
    outJpg    = rest;
    outLocked = locked;
    return true;
}

static void loadLogFile() {
    g_logIndex.clear();
    g_nextEntryNumber = 1;

    FILE* f = fopen(TXT_LOG_PATH, "r");
    if (!f) return;

    char buf[512];
    int lastNum = 0;
    while (fgets(buf, sizeof(buf), f)) {
        std::string line(buf);
        while (!line.empty() && (line.back() == '\n' || line.back() == '\r'))
            line.pop_back();

        int num; std::string bmp, jpg; bool locked;
        if (!parseLogLine(line, num, bmp, jpg, locked)) continue;

        LogEntry& entry = g_logIndex[bmp];
        entry.number  = num;
        entry.jpgPath = jpg;
        entry.locked  = locked;

        lastNum = num;
    }
    fclose(f);

    g_nextEntryNumber = lastNum + 1;
}

static bool readExifUserCommentNumber(const char* jpgPath, int& outNumber) {
    FILE* f = fopen(jpgPath, "rb");
    if (!f) return false;

    fseek(f, 0, SEEK_END);
    long fsize = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (fsize < 4) { fclose(f); return false; }

    std::vector<unsigned char> data((size_t)fsize);
    size_t rd = fread(data.data(), 1, (size_t)fsize, f);
    fclose(f);
    if (rd != (size_t)fsize) return false;

    if (data.size() < 2 || data[0] != 0xFF || data[1] != 0xD8) return false;

    size_t pos = 2;
    const unsigned char* exifData = nullptr;
    size_t exifLen = 0;
    while (pos + 4 <= data.size()) {
        if (data[pos] != 0xFF) { pos++; continue; }
        uint8_t marker = data[pos + 1];
        if (marker == 0xD8 || marker == 0xD9) { pos += 2; continue; }
        if (marker == 0x01 || (marker >= 0xD0 && marker <= 0xD7)) { pos += 2; continue; }
        uint16_t segLen = (uint16_t)((data[pos + 2] << 8) | data[pos + 3]);
        if (segLen < 2 || pos + 2 + segLen > data.size()) break;
        if (marker == 0xE1 && segLen >= 8 && memcmp(&data[pos + 4], "Exif\0\0", 6) == 0) {
            exifData = &data[pos + 4 + 6];
            exifLen  = segLen - 2 - 6;
            break;
        }
        if (marker == 0xDA) break;
        pos += 2 + segLen;
    }
    if (!exifData || exifLen < 8) return false;

    bool bigEndian;
    if (exifData[0] == 'M' && exifData[1] == 'M') bigEndian = true;
    else if (exifData[0] == 'I' && exifData[1] == 'I') bigEndian = false;
    else return false;

    auto rd16 = [&](size_t off) -> uint16_t {
        return bigEndian ? (uint16_t)((exifData[off] << 8) | exifData[off + 1])
                          : (uint16_t)((exifData[off + 1] << 8) | exifData[off]);
    };
    auto rd32 = [&](size_t off) -> uint32_t {
        if (bigEndian)
            return (uint32_t(exifData[off]) << 24) | (uint32_t(exifData[off + 1]) << 16) |
                   (uint32_t(exifData[off + 2]) << 8) | exifData[off + 3];
        return (uint32_t(exifData[off + 3]) << 24) | (uint32_t(exifData[off + 2]) << 16) |
               (uint32_t(exifData[off + 1]) << 8) | exifData[off];
    };

    uint32_t ifd0Off = rd32(4);
    if (ifd0Off + 2 > exifLen) return false;

    uint16_t ifd0Count = rd16(ifd0Off);
    uint32_t exifIfdOff = 0;
    bool haveExifIfd = false;
    for (int i = 0; i < ifd0Count; i++) {
        size_t entryOff = ifd0Off + 2 + (size_t)i * 12;
        if (entryOff + 12 > exifLen) break;
        if (rd16(entryOff) == 0x8769) {
            exifIfdOff = rd32(entryOff + 8);
            haveExifIfd = true;
            break;
        }
    }
    if (!haveExifIfd || exifIfdOff + 2 > exifLen) return false;

    uint16_t subCount = rd16(exifIfdOff);
    for (int i = 0; i < subCount; i++) {
        size_t entryOff = exifIfdOff + 2 + (size_t)i * 12;
        if (entryOff + 12 > exifLen) break;
        if (rd16(entryOff) != 0x9286) continue;

        uint32_t count  = rd32(entryOff + 4);
        uint32_t dataOff = rd32(entryOff + 8);
        if (count < 8 || dataOff + count > exifLen) return false;

        size_t textOff = dataOff + 8;
        size_t textLen = count - 8;
        if (textLen == 0) return false;

        std::string text((const char*)&exifData[textOff], textLen);
        size_t p = 0;
        while (p < text.size() && isdigit((unsigned char)text[p])) p++;
        if (p == 0) return false;

        outNumber = atoi(text.substr(0, p).c_str());
        return true;
    }
    return false;
}

static void lockLogEntry(int number, const std::string& bmpName, const std::string& jpgPath) {
    FILE* f = fopen(TXT_LOG_PATH, "rb");
    if (!f) return;
    fseek(f, 0, SEEK_END);
    long fsize = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (fsize <= 0) { fclose(f); return; }
    std::string content((size_t)fsize, '\0');
    size_t rd = fread(&content[0], 1, (size_t)fsize, f);
    fclose(f);
    if (rd != (size_t)fsize) return;

    char numBuf[16];
    snprintf(numBuf, sizeof(numBuf), "%d", number);
    std::string target = std::string(numBuf) + " - " + bmpName + " >> " + jpgPath;

    size_t pos = content.find(target);
    while (pos != std::string::npos) {
        bool atLineStart = (pos == 0) || content[pos - 1] == '\n';
        if (atLineStart) break;
        pos = content.find(target, pos + 1);
    }
    if (pos == std::string::npos) return;

    content.insert(pos + target.size(), " X");

    FILE* out = fopen(TXT_LOG_PATH, "wb");
    if (!out) return;
    fwrite(content.data(), 1, content.size(), out);
    fclose(out);
}

static void appendLogEntry(int number, const std::string& bmpName, const std::string& jpgRelPath) {
    struct stat st;
    bool exists = (stat(TXT_LOG_PATH, &st) == 0);

    FILE* f = fopen(TXT_LOG_PATH, "a");
    if (!f) return;

    if (!exists) {
        fprintf(f, "Following entries are screenshots that were converted to JPEG by SCR2JPG for 3DS by Adrix12team - github.com/Adrix12team/SCR2JPG\r\n");
        fprintf(f, "If you do not know what you are doing, ignore and don't delete/modify this file, except you want to have duplicate screenshots!\r\n");
    }

    fprintf(f, "%d - %s >> %s\r\n", number, bmpName.c_str(), jpgRelPath.c_str());
    fclose(f);
}

static bool shouldSkipConversion(const std::string& bmpName) {
    auto it = g_logIndex.find(bmpName);
    if (it == g_logIndex.end()) return false;

    if (it->second.locked) return true;

    std::string fullJpgPath = std::string(DCIM_BASE) + it->second.jpgPath;
    struct stat st;
    if (stat(fullJpgPath.c_str(), &st) != 0) return false;

    int exifNum;
    if (!readExifUserCommentNumber(fullJpgPath.c_str(), exifNum)) return false;
    if (exifNum != it->second.number) return false;

    return true;
}

// Wie shouldSkipConversion(), aber für ein _top/_top_right-Paar, das
// gemeinsam in einer MPO-Datei landet: nur überspringen, wenn BEIDE
// BMP-Namen bereits (gültig) auf dieselbe Ausgabedatei verweisen.
static bool shouldSkipPairConversion(const std::string& topName, const std::string& rightName) {
    auto itTop   = g_logIndex.find(topName);
    auto itRight = g_logIndex.find(rightName);
    if (itTop == g_logIndex.end() || itRight == g_logIndex.end()) return false;
    if (itTop->second.jpgPath != itRight->second.jpgPath) return false;
    return shouldSkipConversion(topName) && shouldSkipConversion(rightName);
}

// ==================== UI HELPERS ====================
static void drawProgressBar(int done, int total, int barW) {
    int filled = (total > 0) ? (done * barW / total) : 0;
    printf("[");
    for (int i = 0; i < barW; i++) printf(i < filled ? "#" : "-");
    printf("] %3d%%", total > 0 ? (done * 100 / total) : 0);
}

static void drawTopHeader(const char* status, int done, int total,
                          int ok, int skipped, bool deleteMode) {
    consoleSelect(&topScreen);
    printf("\x1b[1;1H");

    printf("\x1b[94m==================================================\x1b[0m\n");
    printf("\x1b[94m|        SCR2JPG        || Screenshots to Camera |\x1b[0m\n");
    printf("\x1b[94m==================================================\x1b[0m\n");

    printf(" Status : %s                                                               \n", status);
    printf(" Files  : %d / %d  (\x1b[32mOK: %d\x1b[0m  \x1b[31mSkipped: %d\x1b[0m)                             \n",
           done, total, ok, skipped);

    printf(" ");
    drawProgressBar(done, total, 36);
    printf("\n\n");

    printf(" Mode   : %s\n",
           deleteMode ? "\x1b[31mDelete originals after conversion\x1b[0m"
                      : "\x1b[32mKeep originals after conversion\x1b[0m");

    printf("\x1b[94m==================================================\x1b[0m\n");
}

// ==================== MAIN ====================
int main() {
    gfxInitDefault();
    consoleInit(GFX_TOP,    &topScreen);
    consoleInit(GFX_BOTTOM, &bottomScreen);

    for (int i = 0; i < 120; i++) {
        hidScanInput();
        gspWaitForVBlank();
    }

    bool deleteOriginals = false;
    bool readyToStart    = false;

    // ---- Settings screen ----
    while (aptMainLoop() && !readyToStart) {
        hidScanInput();
        u32 kDown = hidKeysDown();
        if (kDown & KEY_DUP)   deleteOriginals = true;
        if (kDown & KEY_DDOWN) deleteOriginals = false;
        if (kDown & KEY_A)     readyToStart    = true;
        if (kDown & KEY_START) { gfxExit(); return 0; }

        consoleSelect(&topScreen);
        printf("\x1b[1;1H");
        printf("\x1b[94m==================================================\x1b[0m\n");
        printf("\x1b[94m|        SCR2JPG        || Screenshots to Camera |\x1b[0m\n");
        printf("\x1b[94m==================================================\x1b[0m\n");
        printf("\n");
        printf("  Converts Luma3DS screenshots (BMP) to\n");
        printf("  Nintendo DCIM JPEG with EXIF metadata.\n");
        printf("  Source : sdmc:/luma/screenshots/\n");
        printf("  Output : sdmc:/DCIM/###NIN03/HNI_####.JPG\n");
        printf("\n");
        printf("\x1b[94m  ---- After conversion ----\x1b[0m\n\n");
        printf("  %s \x1b[31mDelete\x1b[0m original BMP files\n",
               deleteOriginals  ? "\x1b[32m[x]\x1b[0m" : "[ ]");
        printf("  %s \x1b[32mKeep\x1b[0m   original BMP files\n",
               !deleteOriginals ? "\x1b[32m[x]\x1b[0m" : "[ ]");
        printf("\n");
        printf("\x1b[94m==================================================\x1b[0m\n");

        consoleSelect(&bottomScreen);
        printf("\x1b[1;1H");
        printf("\x1b[94m  CONTROLS: --------------------------\x1b[0m\n");
        printf("  D-Pad Up/Down       Select mode\n");
        printf("  A                   Start conversion\n");
        printf("  START               Exit\n");

        gfxFlushBuffers();
        gfxSwapBuffers();
        gspWaitForVBlank();
    }

    // ---- Conversion ----
    consoleSelect(&topScreen);
    consoleClear();
    consoleSelect(&bottomScreen);
    consoleClear();
    mkdir(DCIM_BASE, 0777);
    loadLogFile();

    std::vector<std::string> files;
    DIR* d = opendir(SRC_DIR);
    if (d) {
        struct dirent* e;
        while ((e = readdir(d)))
            if (isBmp(e->d_name))
                files.push_back(std::string(SRC_DIR) + e->d_name);
        closedir(d);
    }

    int okCount      = 0;
    int skippedCount = 0;
    int total        = (int)files.size();

    // ---- 3D-Paare erkennen ----
    // _top.bmp + _top_right.bmp mit demselben Zeitstempel-Präfix werden zu
    // EINER MPO-Datei kombiniert. _bottom.bmp (und jedes unpaarige top /
    // top_right) läuft unverändert über den bestehenden Einzelbild-Pfad.
    std::vector<int>  mpoPartner(total, -1);   // Index von _top -> Index des zugehörigen _top_right
    std::vector<bool> skipIndex(total, false); // _top_right-Indizes, die bereits als Teil eines Paares laufen
    {
        struct PairSlot { int topIdx = -1; int topRightIdx = -1; };
        std::map<std::string, PairSlot> pairMap;
        for (int i = 0; i < total; i++) {
            size_t slashPos = files[i].find_last_of('/');
            std::string fname = (slashPos != std::string::npos) ? files[i].substr(slashPos + 1) : files[i];
            std::string prefix, suffix;
            if (!getFilePrefixAndSuffix(fname, prefix, suffix)) continue;
            if (suffix == "_top.bmp")            pairMap[prefix].topIdx = i;
            else if (suffix == "_top_right.bmp") pairMap[prefix].topRightIdx = i;
        }
        for (auto& kv : pairMap) {
            const PairSlot& slot = kv.second;
            if (slot.topIdx != -1 && slot.topRightIdx != -1) {
                mpoPartner[slot.topIdx]     = slot.topRightIdx;
                skipIndex[slot.topRightIdx] = true;
            }
        }
    }

    if (files.empty()) {
        drawTopHeader("No BMP files found.", 0, 0, 0, 0, deleteOriginals);
        consoleSelect(&bottomScreen);
        printf("\x1b[31m  No screenshots in sdmc:/luma/screenshots/\x1b[0m\n");
        printf("  Take some screenshots first (L + D-Pad Down + SELECT).\n");
    } else {
        drawTopHeader("Starting...", 0, total, 0, 0, deleteOriginals);

        for (int i = 0; i < total; i++) {
            if (skipIndex[i]) continue; // bereits zusammen mit seinem _top-Partner verarbeitet

            size_t slashPos = files[i].find_last_of('/');
            std::string fname = (slashPos != std::string::npos) ? files[i].substr(slashPos + 1) : files[i];

            if (mpoPartner[i] != -1) {
                // ==================== 3D-PAAR -> EINE MPO-DATEI ====================
                int j = mpoPartner[i];
                size_t slashPosR = files[j].find_last_of('/');
                std::string fnameRight = (slashPosR != std::string::npos) ? files[j].substr(slashPosR + 1) : files[j];

                if (shouldSkipPairConversion(fname, fnameRight)) {
                    skippedCount += 2;
                    consoleSelect(&bottomScreen);
                    printf("\x1b[33m  [SKIP]\x1b[0m %s + %s\n", fname.c_str(), fnameRight.c_str());

                    if (i % 5 == 0 || i == total - 1) {
                        char statusBuf[48];
                        snprintf(statusBuf, sizeof(statusBuf), "Converting... (%d left)", total - i - 1);
                        drawTopHeader(i == total - 1 ? "Done!" : statusBuf,
                                      i + 1, total, okCount, skippedCount, deleteOriginals);
                    }
                    gfxFlushBuffers();
                    gfxSwapBuffers();
                    gspWaitForVBlank();
                    continue;
                }

                if (!hasEnoughSpace()) {
                    drawTopHeader("ERROR: SD card full!", i, total, okCount, skippedCount, deleteOriginals);
                    consoleSelect(&bottomScreen);
                    printf("\x1b[31m  [ERR] SD card full - aborting.\x1b[0m\n");
                    break;
                }

                char outPath[256];
                if (!getNextOutputPath(outPath, sizeof(outPath), "MPO")) {
                    drawTopHeader("ERROR: DCIM full!", i, total, okCount, skippedCount, deleteOriginals);
                    consoleSelect(&bottomScreen);
                    printf("\x1b[31m  [ERR] DCIM directory full.\x1b[0m\n");
                    break;
                }

                int wTop, hTop, wRight, hRight;
                auto rgbTop   = loadBmp(files[i].c_str(), wTop, hTop);
                auto rgbRight = loadBmp(files[j].c_str(), wRight, hRight);
                bool success = false;
                if (!rgbTop.empty() && !rgbRight.empty()) {
                    char datetimeTop[20], datetimeRight[20];
                    parseTimestampFromFilename(files[i], getOffsetSecondsForFilename(fname),      datetimeTop);
                    parseTimestampFromFilename(files[j], getOffsetSecondsForFilename(fnameRight), datetimeRight);
                    success = saveMpo(outPath, rgbTop, wTop, hTop, datetimeTop,
                                               rgbRight, wRight, hRight, datetimeRight,
                                               g_nextEntryNumber);
                }

                consoleSelect(&bottomScreen);
                if (success) {
                    okCount += 2;
                    std::string relMpo = shortenJpgPath(outPath);

                    // Alte Log-Zeilen (falls vorhanden) einzeln sperren - top und
                    // top_right können vorher unterschiedliche alte Einträge gehabt haben.
                    // Falls dabei ein BMP vorher als EIGENSTÄNDIGES JPG konvertiert wurde
                    // (jetzt aber Teil dieses MPO-Paares ist), wird die verwaiste Datei
                    // von der SD-Karte entfernt, damit nicht zusätzlich ein Einzelbild
                    // desselben Fotos in der Galerie herumliegt.
                    auto itT = g_logIndex.find(fname);
                    if (itT != g_logIndex.end()) {
                        lockLogEntry(itT->second.number, fname, itT->second.jpgPath);
                        if (itT->second.jpgPath != relMpo) {
                            remove((std::string(DCIM_BASE) + itT->second.jpgPath).c_str());
                        }
                    }
                    auto itR = g_logIndex.find(fnameRight);
                    if (itR != g_logIndex.end()) {
                        lockLogEntry(itR->second.number, fnameRight, itR->second.jpgPath);
                        if (itR->second.jpgPath != relMpo) {
                            remove((std::string(DCIM_BASE) + itR->second.jpgPath).c_str());
                        }
                    }

                    // Beide Quellnamen zeigen auf dieselbe entryNumber & MPO-Datei.
                    appendLogEntry(g_nextEntryNumber, fname, relMpo);
                    appendLogEntry(g_nextEntryNumber, fnameRight, relMpo);

                    g_logIndex[fname]      = { g_nextEntryNumber, relMpo, false };
                    g_logIndex[fnameRight] = { g_nextEntryNumber, relMpo, false };
                    g_nextEntryNumber++;

                    if (deleteOriginals) { remove(files[i].c_str()); remove(files[j].c_str()); }
                    printf("\x1b[32m  [OK 3D]\x1b[0m %s\n", outPath);
                } else {
                    skippedCount += 2;
                    printf("\x1b[31m  [FAIL]\x1b[0m %s + %s\n", files[i].c_str(), files[j].c_str());
                }

                if (i % 5 == 0 || i == total - 1) {
                    char statusBuf[48];
                    snprintf(statusBuf, sizeof(statusBuf), "Converting... (%d left)", total - i - 1);
                    drawTopHeader(i == total - 1 ? "Done!" : statusBuf,
                                  i + 1, total, okCount, skippedCount, deleteOriginals);
                }

                gfxFlushBuffers();
                gfxSwapBuffers();
                gspWaitForVBlank();
                continue;
            }

            // ==================== EINZELBILD (bottom, oder unpaired top/top_right) ====================
            // 1. CHECKS DURCHFÜHREN
            if (shouldSkipConversion(fname)) {
                skippedCount++;
                consoleSelect(&bottomScreen);
                printf("\x1b[33m  [SKIP]\x1b[0m %s\n", fname.c_str());

                if (i % 5 == 0 || i == total - 1) {
                    char statusBuf[48];
                    snprintf(statusBuf, sizeof(statusBuf), "Converting... (%d left)", total - i - 1);
                    drawTopHeader(i == total - 1 ? "Done!" : statusBuf,
                                  i + 1, total, okCount, skippedCount, deleteOriginals);
                }
                gfxFlushBuffers();
                gfxSwapBuffers();
                gspWaitForVBlank();
                continue;
            }

            if (!hasEnoughSpace()) {
                drawTopHeader("ERROR: SD card full!", i, total, okCount, skippedCount, deleteOriginals);
                consoleSelect(&bottomScreen);
                printf("\x1b[31m  [ERR] SD card full - aborting.\x1b[0m\n");
                break;
            }

            char outPath[256];
            if (!getNextOutputPath(outPath, sizeof(outPath), "JPG")) {
                drawTopHeader("ERROR: DCIM full!", i, total, okCount, skippedCount, deleteOriginals);
                consoleSelect(&bottomScreen);
                printf("\x1b[31m  [ERR] DCIM directory full.\x1b[0m\n");
                break;
            }

            int w, h;
            auto rgb = loadBmp(files[i].c_str(), w, h);
            bool success = false;
            if (!rgb.empty()) {
                int offsetSec = getOffsetSecondsForFilename(fname);
                char datetime[20];
                parseTimestampFromFilename(files[i], offsetSec, datetime);
                // 2. SAVEJPEG MIT ENTRY NUMBER AUFRUFEN
                success = saveJpeg(outPath, rgb, w, h, datetime, g_nextEntryNumber);
            }

            consoleSelect(&bottomScreen);
            if (success) {
                okCount++;
                std::string relJpg = shortenJpgPath(outPath);

                // 3. WENN ALTER EINTRAG EXISTIERT -> ALTE ZEILE MIT X SPPERREN (REKONVERTIERUNG)
                auto it = g_logIndex.find(fname);
                if (it != g_logIndex.end()) {
                    lockLogEntry(it->second.number, fname, it->second.jpgPath);
                }

                // 4. NEUEN LOG-EINTRAG ANHÄNGEN & COUNTER ERHÖHEN
                appendLogEntry(g_nextEntryNumber, fname, relJpg);

                // RAM-Index aktualisieren
                g_logIndex[fname] = { g_nextEntryNumber, relJpg, false };
                g_nextEntryNumber++;

                if (deleteOriginals) remove(files[i].c_str());
                printf("\x1b[32m  [OK]\x1b[0m %s\n", outPath);
            } else {
                skippedCount++;
                printf("\x1b[31m  [FAIL]\x1b[0m %s\n", files[i].c_str());
            }

            if (i % 5 == 0 || i == total - 1) {
                char statusBuf[48];
                snprintf(statusBuf, sizeof(statusBuf), "Converting... (%d left)", total - i - 1);
                drawTopHeader(i == total - 1 ? "Done!" : statusBuf,
                              i + 1, total, okCount, skippedCount, deleteOriginals);
            }

            gfxFlushBuffers();
            gfxSwapBuffers();
            gspWaitForVBlank();
        }
    }

    // ---- Done screen ----
    drawTopHeader("Done!", total, total, okCount, skippedCount, deleteOriginals);
    consoleSelect(&bottomScreen);
    printf("\n\x1b[32m  Conversion complete.\x1b[0m\n");
    printf("  Converted : %d\n", okCount);
    printf("  Skipped   : %d\n", skippedCount);
    printf("\n  Press START to exit.\n");

    gfxFlushBuffers();
    gfxSwapBuffers();

    while (aptMainLoop()) {
        hidScanInput();
        if (hidKeysDown() & KEY_START) break;
        gspWaitForVBlank();
    }

    gfxExit();
    return 0;
}
