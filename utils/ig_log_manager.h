#pragma once

#include <string>
#include <fstream>
#include <memory>
#include <vector>
#include <chrono>
#include <filesystem>
#include <nlohmann/json.hpp>
#include "options/options.h"

namespace pono {

class IGLogManager {
public:
  IGLogManager(const PonoOptions & opts, const std::string & base_path = "logs/ic3ng");
  ~IGLogManager();

  // Log data to the current chunk
  void log_data(const nlohmann::ordered_json & data);

  // Flush current chunk to disk
  void flush();

private:
  // Create a new chunk file
  void create_new_chunk();

  // Compress the given file using gzip
  void compress_file(const std::string & file_path);

  const PonoOptions & opts_;  // Reference to options
  std::string base_path_;     // Base path for log files
  std::string current_chunk_path_;  // Current chunk file path
  size_t current_size_;       // Current chunk size in bytes
  size_t chunk_count_;        // Number of chunks created
  std::ofstream current_file_;  // Current output file stream
  std::vector<nlohmann::ordered_json> buffer_;  // Buffer for JSON data
  bool compress_enabled_;     // Store the initial compression setting

  // Constants
  static constexpr size_t BUFFER_SIZE = 100;  // Number of entries to buffer before writing
  static constexpr size_t BYTES_PER_MB = 1024 * 1024;
};

} // namespace pono
