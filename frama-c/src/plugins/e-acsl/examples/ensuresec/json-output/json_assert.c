#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#ifdef E_ACSL_CONCURRENCY_PTHREAD
#  include <pthread.h>
#endif

#include <e_acsl.h>

extern int __e_acsl_sound_verdict;

/*! Print to `output` the unicode string `str` as a json string, meaning all
    unicode characters from `\x00` to `\x1f` are escaped, along with newlines,
    tabulations, `"` and some others. */
void json_print_escaped_str(FILE *output, const char *str) {
  for (char *c = (char *)&str[0]; *c != '\0'; ++c) {
    switch (*c) {
    case '"':
      fprintf(output, "%s", "\\\"");
      break;
    case '\\':
      fprintf(output, "%s", "\\\\");
      break;
    case '\b':
      fprintf(output, "%s", "\\b");
      break;
    case '\f':
      fprintf(output, "%s", "\\f");
      break;
    case '\n':
      fprintf(output, "%s", "\\n");
      break;
    case '\r':
      fprintf(output, "%s", "\\r");
      break;
    case '\t':
      fprintf(output, "%s", "\\t");
      break;
    default:
      if ('\x00' <= *c && *c <= '\x1f') {
        fprintf(output, "\\u%04x", (unsigned int)*c);
      } else {
        fprintf(output, "%c", *c);
      }
    }
  }
}

/*! Print the given value to `output` as a json object. */
void json_print_value(FILE *output, __e_acsl_assert_data_value_t *value) {
  fprintf(output, "          { \"name\": \"");
  json_print_escaped_str(output, value->name);
  fprintf(output, "\", \"value\": \"");
  eacsl_print_value_content(output, value);
  fprintf(output, "\" }");
}

#ifdef E_ACSL_CONCURRENCY_PTHREAD
/*! Global lock for accessing the output json file. */
static pthread_mutex_t ensuresec_mutex = PTHREAD_MUTEX_INITIALIZER;
#  define ENSURESEC_LOCK()   pthread_mutex_lock(&ensuresec_mutex)
#  define ENSURESEC_UNLOCK() pthread_mutex_unlock(&ensuresec_mutex)
#else
#  define ENSURESEC_LOCK()                                                     \
    do {                                                                       \
    } while (0)
#  define ENSURESEC_UNLOCK()                                                   \
    do {                                                                       \
    } while (0)
#endif

/*! Assert macro to output `msg` to `stderr` if `pred` is false. The output does
    not allocate. */
#define ENSURESEC_ASSERT(pred, msg)                                            \
  do {                                                                         \
    if (!(pred)) {                                                             \
      const char m[] = msg;                                                    \
      write(STDERR_FILENO, m, sizeof(m) - 1);                                  \
      abort();                                                                 \
    }                                                                          \
  } while (0)

/*! Json output file. */
static FILE *ensuresec_output_file;
/*! String to use for Ensuresec e-commerce ecosystem id (EE id) field. */
static const char *ensuresec_ee_id;
/*! String to use for Ensuresec e-commerce ecosystem tool id (EE tool id) field. */
static const char *ensuresec_ee_tool_id;

/*! \brief Finalize ensuresec output.

    - Print the closing bracket of the json array.
    - Flush the output. */
void ensuresec_clean_assert() {
  fprintf(ensuresec_output_file, "]\n");
  int result = fflush(ensuresec_output_file);
  ENSURESEC_ASSERT(result == 0, "Unable to flush ENSURESEC_OUTPUT_FILE\n");

  // Purposefully do not close the json ouptut file: on normal termination, this
  // function will be called after the return in `main()` and the shadow
  // memories of E-ACSL will already be destroyed, resulting in a segmentation
  // fault.
  // The OS will automatically close the file descriptor and reclaim allocated
  // memory on program termination.
}

/*! \brief Initialize ensuresec output.

    - Retrieve the EE id and EE tool id from the environment variables
      `ENSURESEC_EE_ID` and `ENSURESEC_EE_TOOL_ID`.
    - Retrieve the path to the json output file from the environment variable
      `ENSURESEC_OUTPUT_FILE`.
    - Open the json output file.
    - Print an opening bracket for a json array.
    - Register the cleaning function to be called on normal program termination.
*/
void ensuresec_init_assert() {
  ensuresec_ee_id = getenv("ENSURESEC_EE_ID");
  ENSURESEC_ASSERT(ensuresec_ee_id != NULL,
                   "Unable to retrieve env var ENSURESEC_EE_ID\n");

  ensuresec_ee_tool_id = getenv("ENSURESEC_EE_TOOL_ID");
  ENSURESEC_ASSERT(ensuresec_ee_tool_id != NULL,
                   "Unable to retrieve env var ENSURESEC_EE_TOOL_ID\n");

  const char *filename = getenv("ENSURESEC_OUTPUT_FILE");
  ENSURESEC_ASSERT(filename != NULL,
                   "Unable to retrieve env var ENSURESEC_OUTPUT_FILE\n");
  if (strcmp(filename, "-") == 0) {
    ensuresec_output_file = stdout;
  } else {
    ensuresec_output_file = fopen(filename, "w");
  }
  ENSURESEC_ASSERT(ensuresec_output_file != NULL,
                   "Unable to open ENSURESEC_OUTPUT_FILE\n");

  fprintf(ensuresec_output_file, "[\n");

  // The function ensuresec_clean_assert will be called on normal program
  // termination (via exit() or returning from main())
  atexit(ensuresec_clean_assert);
}

/*! \brief __e_acsl_assert override to print output in a json file. */
void __e_acsl_assert(int predicate, __e_acsl_assert_data_t *data) {
  // Initialize output file only once per program execution
#ifdef E_ACSL_CONCURRENCY_PTHREAD
  static pthread_once_t already_run = PTHREAD_ONCE_INIT;
  int result = pthread_once(&already_run, ensuresec_init_assert);
  ENSURESEC_ASSERT(result == 0, "Unable to initialize __e_acsl_assert\n");
#else
  static int already_run = 0;
  if (!already_run) {
    ensuresec_init_assert();
    already_run = 1;
  }
#endif

#ifndef E_ACSL_DEBUG_ASSERT
  if (!__e_acsl_sound_verdict || !predicate)
#endif
  {
    ENSURESEC_LOCK();
    // Id of the alert
    static size_t alert_id = 0;

    // We just want a smaller var for clearer source code
    FILE *o = ensuresec_output_file;

    // If this is not the first alert, we need to add a comma between the
    // previous json object and the one we will print now
    if (alert_id > 0) {
      fprintf(o, ",\n");
    }

    // Start printing the alert
    fprintf(o, "{\n");
    fprintf(o, "  \"version\": \"1.0\",\n");
    fprintf(o, "  \"partner\": \"CEA\",\n");
    fprintf(o, "  \"id\": \"CEA/Frama-C\",\n");
    fprintf(o, "  \"alert\": {\n");
    fprintf(o, "    \"id\": \"%d\",\n", alert_id++);
    fprintf(o, "    \"type\": \"%s/%s\",\n", data->kind,
            data->name ? data->name : "");

    // Print current time as an ISO8601 date
    time_t t = time(NULL);
    char timebuf[32]; // Enough space to print an ISO8601 date
    strftime(timebuf, sizeof(timebuf), "%FT%T", gmtime(&t));
    fprintf(o, "    \"startTS\": \"%s\",\n", timebuf);
    fprintf(o, "    \"endTS\": \"%s\",\n", timebuf);

    fprintf(o, "    \"eCommerceEcoId\": \"%s\",\n", ensuresec_ee_id);

    // Infer the severity of the alert from its kind:
    // - RTE index out of bound or memory access: HIGH
    // - Other RTE: MEDIUM
    // - Assertions from the Frama-C libc: MEDIUM
    // - User assertions: LOW
    static const char *severities[] = {"LOW", "MEDIUM", "HIGH"};
    int severity_idx = 0;
    if (strcmp(data->kind, "RTE") == 0) {
      if (strcmp(data->name, "index_bound") == 0
          || strcmp(data->name, "mem_access") == 0) {
        severity_idx = 2;
      } else {
        severity_idx = 1;
      }
    } else if (strstr(data->file, "FRAMAC_SHARE/libc") != NULL) {
      severity_idx = 1;
    }

    fprintf(o, "    \"severity\": \"%s\",\n", severities[severity_idx]);

    fprintf(o, "    \"EE_Element\": [{\n");
    fprintf(o, "      \"id\": \"%s:%d\",\n", data->file, data->line);
    fprintf(o, "      \"elementType\": \"EEAsset\",\n");
    fprintf(o, "      \"assetType\": \"cyber/CSourceFile\"\n");
    fprintf(o, "    }],\n");

    fprintf(o, "    \"detector\": {\n");
    fprintf(o, "      \"type\": \"cyber/RuntimeVerification\",\n");
    fprintf(o, "      \"providerId\": \"CEA\",\n");
    fprintf(o, "      \"sourceId\": \"%s\"\n", ensuresec_ee_tool_id);
    fprintf(o, "    },\n");
    fprintf(o, "    \"data\": [{\n");
    fprintf(o, "      \"contentType\": \"JsonData\",\n");
    fprintf(o, "      \"type\": \"AssertionData\",\n");
    fprintf(o, "      \"startTS\": \"%s\",\n", timebuf);
    fprintf(o, "      \"endTS\": \"%s\",\n", timebuf);
    fprintf(o, "      \"creationTS\": \"%s\",\n", timebuf);
    fprintf(o, "      \"dataSource\": {\n");
    fprintf(o, "        \"dataSourceType\": \"Detector\",\n");
    fprintf(o, "        \"type\": \"cyber/RuntimeVerification\",\n");
    fprintf(o, "        \"providerId\": \"CEA\",\n");
    fprintf(o, "        \"sourceId\": \"%s\"\n", ensuresec_ee_tool_id);
    fprintf(o, "      },\n");

    // Details of the assertion
    fprintf(o, "      \"jsonContent\": {\n");
    // Kind of verdict
    fprintf(o, "        \"verdict\": \"%s%s%s\",\n",
            __e_acsl_sound_verdict ? "" : "unsound ",
            predicate ? "valid" : "invalid",
            data->blocking ? "" : " (non-blocking)");
    // Kind and name of the assertion
    fprintf(o, "        \"kind\": \"%s\",\n", data->kind);
    fprintf(o, "        \"name\": \"%s\",\n", data->name ? data->name : "");
    // Content of the predicate
    fprintf(o, "        \"predicate\": \"");
    json_print_escaped_str(o, data->pred_txt);
    fprintf(o, "\",\n");
    // Location in the source code
    fprintf(o, "        \"location\": {\n");
    fprintf(o, "          \"file\": \"%s\",\n", data->file);
    fprintf(o, "          \"line\": \"%d\",\n", data->line);
    fprintf(o, "          \"function\": \"%s\"\n", data->fct);
    fprintf(o, "        },\n");
    // Values of the assertion
    fprintf(o, "        \"values\": [\n");
    __e_acsl_assert_data_value_t *value = data->values;
    while (value != NULL) {
      json_print_value(o, value);
      value = value->next;
      if (value) {
        fprintf(o, ",\n");
      } else {
        fprintf(o, "\n");
      }
    }
    fprintf(o, "        ]\n");
    fprintf(o, "      }\n");

    // Close the alert
    fprintf(o, "    }]\n");
    fprintf(o, "  }\n");
    fprintf(o, "}\n");
    fflush(o);

    if (data->blocking && __e_acsl_sound_verdict && !predicate) {
#ifndef E_ACSL_NO_ASSERT_FAIL
#  ifdef E_ACSL_FAIL_EXITCODE
      exit(E_ACSL_FAIL_EXITCODE);
#  else
      // If we are aborting then we need to manually call the cleanup function
      ensuresec_clean_assert();
      abort();
#  endif
#endif
    }

    ENSURESEC_UNLOCK();
  }
}
