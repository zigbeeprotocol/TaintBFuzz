# -*- coding: utf-8 -*-

# Test server that listen on URL /alert for JSON emitted by a program monitored
# by E-ACSL and print received alerts to the console output.
# Run with `FLASK_APP=receiver.py FLASK_ENV=development flask run`

from flask import Flask, request

app = Flask(__name__)


@app.post("/alert")
def add_alert():
    if request.is_json:
        alert = request.get_json()
        content = alert['alert']['data'][0]['jsonContent']
        print(
"""{file}: In function '{fct}'
{file}:{line}: {kind} {verdict}:
\t{name}{post_name}{predicate}"""
              .format(
                  file=content['location']['file'],
                  fct=content['location']['function'],
                  line=content['location']['line'],
                  kind=content['kind'],
                  verdict=content['verdict'],
                  name=content['name'],
                  post_name=":\n\t" if content['name'] else "",
                  predicate=content['predicate']
              ))
        if content['values']:
            print("\tWith values:")
            for value in content['values']:
                print("\t- {}: {}".format(value['name'], value['value']))
        return {}, 201
    return {"error": "Request must be JSON."}, 415
