#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# Wrapper for an E-ACSL monitored executable that will POST each raised alert
# to a specific URL.

import argparse
import dotenv
import ijson
import os
import requests
import subprocess

ALERT_URL = 'ENSURESEC_ALERT_URL'
EE_ID = 'ENSURESEC_EE_ID'
EE_TOOL_ID = 'ENSURESEC_EE_TOOL_ID'


def check_config(value, name):
    """Check if the given value is empty and exit with an error message if that
    is the case."""
    if not value:
        print("The '{}' option should be provided and not empty.".format(name))
        exit(1)


@ijson.coroutine
def send_alert(url):
    """send_alert() is a coroutine that will process E-ACSL alerts as they are
    emitted by the program. The JSON alerts are POST-ed to the given URL."""
    while True:
        alert = (yield)
        r = requests.post(url, json=alert)
        if not r.ok:
            print("Error while sending alert: " + r.text)


def main():
    default = {
        # Default empty values
        ALERT_URL: '',
        EE_ID: '',
        EE_TOOL_ID: '',
        # Read configuration from .env file if it exists
        **dotenv.dotenv_values(".env"),
        # Overwrite with environment variables
        **os.environ
    }

    # Parse script arguments
    parser = argparse.ArgumentParser(
        description="Wrapper for an E-ACSL monitored executable that will POST \
                     each raised alert to a specific URL.")
    parser.add_argument(
        'program',
        help="E-ACSL program to launch and monitor.")
    parser.add_argument(
        'args',
        help="Arguments for the E-ACSL program.",
        nargs='*')
    parser.add_argument(
        '-u', '--alert-url',
        help="URL where alerts raised by the E-ACSL program must be pushed, \
              default to environment variable {}.".format(ALERT_URL),
        metavar='url',
        default=default[ALERT_URL],
        dest='alert_url')
    parser.add_argument(
        '-i', '--id',
        help="Ensuresec e-commerce ecosystem id, default to environment \
              variable {}.".format(EE_ID),
        metavar='id',
        default=default[EE_ID],
        dest='id')
    parser.add_argument(
        '-t', '--tool-id',
        help="Ensuresec e-commerce ecosystem tool id, default to environment \
              variable {}.".format(EE_TOOL_ID),
        metavar="id",
        default=default[EE_TOOL_ID],
        dest='tool_id')
    config = parser.parse_args()

    # Check that all necessary configurations have been provided
    check_config(config.alert_url, 'alert-url')
    check_config(config.id, 'id')
    check_config(config.tool_id, 'tool-id')

    # Create an environment for the subprocess with the information either
    # retrieved from the configuration or the script arguments, and setup
    # JSON output to stdout
    env = {'ENSURESEC_EE_ID': config.id,
           'ENSURESEC_EE_TOOL_ID': config.tool_id,
           'ENSURESEC_OUTPUT_FILE': '-'}
    # Launch E-ACSL program as a subprocess
    p = subprocess.Popen([config.program] + config.args, stdout=subprocess.PIPE,
                         env=env)

    # Parse output of E-ACSL program as it is produced and use a coroutine to
    # process JSON objects
    coro = ijson.items_coro(send_alert(config.alert_url), 'item')
    for chunk in p.stdout:
        coro.send(chunk)
    coro.close()

    # Wait for the end of E-ACSL program
    p.wait()


if __name__ == "__main__":
    main()
