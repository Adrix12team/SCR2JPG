#include <3ds.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <dirent.h>
#include <sys/stat.h>
#include <sys/statvfs.h>
#include <setjmp.h>
#include <vector>
#include <string>

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

// ==================== FIXED EXIF TEMPLATE ====================
static unsigned char exif_template[] = {
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
    // 0x56: Make (9 chars + 1 null/padding)
    'N','i','n','t','e','n','d','o',0x00, 0x00,
    // 0x60: Model (13 chars + 1 null/padding)
    'N','i','n','t','e','n','d','o',' ','3','D','S',0x00, 0x00,
    // 0x6E: Software (6 chars)
    '0','0','2','2','7',0x00,
    // 0x74: DateTime (20 chars)
    '2','0','0','1',':','0','1',':','0','1',' ','0','0',':','0','0',':','0','0',0x00,
    // 0x88: Artist (16 chars)
    'S','C','R','2','J','P','G',' ','f','o','r',' ','3','D','S',0x00,

    // --- Sub-IFD (ExifIFD) starting at Offset 0x98 ---
    0x00, 0x02,                                     // 2 entries in Sub-IFD
    // 0x9000 ExifVersion (UNDEFINED, 4 bytes, written inline)
    0x90, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00, 0x04, '0','2','2','0',
    // 0x9003 DateTimeOriginal (ASCII, 20 bytes, Offset 0xB6)
    0x90, 0x03, 0x00, 0x02, 0x00, 0x00, 0x00, 0x14, 0x00, 0x00, 0x00, 0xB6,
    
    0x00, 0x00, 0x00, 0x00,                         // Next Sub-IFD offset (none)

    // 0xB6: DateTimeOriginal String (20 chars)
    '2','0','0','1',':','0','1',':','0','1',' ','0','0',':','0','0',':','0','0',0x00,
};

/**
 * Adds the Nintendo 3DS specific Exif data to the JPEG compression stream.
 * Uses marker 0xE1 (APP1).
 */
static void addNintendoExif(jpeg_compress_struct* cinfo) {
    jpeg_write_marker(cinfo, 0xE1, exif_template, sizeof(exif_template));
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

static bool getNextOutputPath(char* outPath, size_t size) {
    for (; g_dirIdx <= 999; g_dirIdx++, g_fileIdx = 1) {
        char dirPath[256];
        snprintf(dirPath, sizeof(dirPath), "%s%03dNIN03", DCIM_BASE, g_dirIdx);
        mkdir(dirPath, 0777);
        for (; g_fileIdx <= MAX_FILES_PER_DIR; g_fileIdx++) {
            snprintf(outPath, size, "%s/HNI_%04d.JPG", dirPath, g_fileIdx);
            struct stat st;
            if (stat(outPath, &st) != 0) {
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
    int srcBpp = hdr.bpp / 8;
    if (hdr.comp != 0 || (srcBpp != 3 && srcBpp != 4)) { fclose(f); return {}; }
    int rowStride = ((w * srcBpp) + 3) & ~3;
    std::vector<uint8_t> rgb(w * h * 3);
    std::vector<uint8_t> rowBuf(rowStride);
    fseek(f, hdr.offset, SEEK_SET);
    for (int y = 0; y < h; y++) {
        if (fread(rowBuf.data(), 1, rowStride, f) != (size_t)rowStride) break;
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

static bool saveJpeg(const char* path, const std::vector<uint8_t>& rgb, int w, int h) {
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
    addNintendoExif(&cinfo);
    while (cinfo.next_scanline < cinfo.image_height) {
        JSAMPROW row = (JSAMPROW)&rgb[cinfo.next_scanline * w * 3];
        jpeg_write_scanlines(&cinfo, &row, 1);
    }
    jpeg_finish_compress(&cinfo);
    jpeg_destroy_compress(&cinfo);

    FILE* f = fopen(path, "wb");
    if (!f) { free(mem_buf); return false; }
    bool ok = (fwrite(mem_buf, 1, mem_size, f) == mem_size);
    fclose(f);
    free(mem_buf);
    return ok;
}

// ==================== LOG FILE ====================
/**
 * Appends successfully converted paths to sdmc:/DCIM/SCR2JPG.txt.
 * Creates the file with a header line if it does not yet exist.
 * Only writes the camera-relevant portion of each path,
 * e.g. "100NIN03/HNI_0001.JPG" instead of the full sdmc:/ URL.
 */
void updateLogFile(const std::vector<std::string>& successfulPaths) {
    if (successfulPaths.empty()) return;

    const char* logPath = "sdmc:/DCIM/SCR2JPG.txt";
    struct stat st;
    bool exists = (stat(logPath, &st) == 0);

    FILE* f = fopen(logPath, "a");
    if (!f) return;

    if (!exists) {
        fprintf(f, "Following pictures were Luma3DS screenshots, converted by SCR2JPG:\r\n");
    }

    for (const auto& fullPath : successfulPaths) {
        size_t lastSlash = fullPath.find_last_of('/');
        if (lastSlash != std::string::npos) {
            size_t secondLastSlash = fullPath.find_last_of('/', lastSlash - 1);
            if (secondLastSlash != std::string::npos) {
                // Extract the part after the second-to-last slash
                // e.g. "sdmc:/DCIM/100NIN03/HNI_0001.JPG" -> "100NIN03/HNI_0001.JPG"
                std::string shortPath = fullPath.substr(secondLastSlash + 1);
                fprintf(f, "%s\r\n", shortPath.c_str());
            } else {
                fprintf(f, "%s\r\n", fullPath.c_str());
            }
        }
    }
    fclose(f);
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

    // Title bar – secondary colour (94)
    printf("\x1b[94m==================================================\x1b[0m\n");
    printf("\x1b[94m|        SCR2JPG        || Screenshots to Camera |\x1b[0m\n");
    printf("\x1b[94m==================================================\x1b[0m\n");

    // Status line – white, status text plain
    printf(" Status : %s                                                               \n", status);

    // Progress counters – OK green, skipped red, rest white
    printf(" Files  : %d / %d  (\x1b[32mOK: %d\x1b[0m  \x1b[31mSkipped: %d\x1b[0m)                             \n",
           done, total, ok, skipped);

    // Progress bar – white
    printf(" ");
    drawProgressBar(done, total, 36);
    printf("\n\n");

    // Mode line – delete=red, keep=green label; key white
    printf(" Mode   : %s\n",
           deleteMode ? "\x1b[31mDelete originals after conversion\x1b[0m"
                      : "\x1b[32mKeep originals after conversion\x1b[0m");

    // Separator – secondary colour (94)
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

        // Top screen – title + options
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

        // Bottom screen – controls
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
    std::vector<std::string> successfulExports; // Stores paths for the log file

    if (files.empty()) {
        drawTopHeader("No BMP files found.", 0, 0, 0, 0, deleteOriginals);
        consoleSelect(&bottomScreen);
        printf("\x1b[31m  No screenshots in sdmc:/luma/screenshots/\x1b[0m\n");
        printf("  Take some screenshots first (L + D-Pad Down + SELECT).\n");
    } else {
        drawTopHeader("Starting...", 0, total, 0, 0, deleteOriginals);

        for (int i = 0; i < total; i++) {
            if (!hasEnoughSpace()) {
                drawTopHeader("ERROR: SD card full!", i, total, okCount, skippedCount, deleteOriginals);
                consoleSelect(&bottomScreen);
                printf("\x1b[31m  [ERR] SD card full - aborting.\x1b[0m\n");
                break;
            }

            char outPath[256];
            if (!getNextOutputPath(outPath, sizeof(outPath))) {
                drawTopHeader("ERROR: DCIM full!", i, total, okCount, skippedCount, deleteOriginals);
                consoleSelect(&bottomScreen);
                printf("\x1b[31m  [ERR] DCIM directory full.\x1b[0m\n");
                break;
            }

            int w, h;
            auto rgb = loadBmp(files[i].c_str(), w, h);
            bool success = false;
            if (!rgb.empty())
                success = saveJpeg(outPath, rgb, w, h);

            consoleSelect(&bottomScreen);
            if (success) {
                okCount++;
                successfulExports.push_back(outPath); // Add path to log list
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

    // Write log file after all conversions are complete
    updateLogFile(successfulExports);

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
