from flask import Flask, request, render_template, make_response
import time
import uuid
from main import evalString, default_env

app = Flask(__name__)


sessions = dict()


def clean_old_sessions():
    global sessions

    keys_to_delete = []
    for session_name, (_, date_created) in sessions.items():
        print(f"Looking at {session_name}")
        if time.time() - date_created > 600:
            print(f"deleting {session_name}")
            keys_to_delete.append(session_name)

    for k in keys_to_delete:
        del sessions[k]

    return


@app.route("/")
def testertester():
    resp = make_response(render_template('index.html'))

    session_name = uuid.uuid4().hex[:6].upper()
    resp.set_cookie('session', session_name)
    sessions[session_name] = (default_env, time.time())
    clean_old_sessions()

    return resp


@ app.route('/clicked')
def clicked():
    return "<p>Clicked</p>"


@ app.route('/put', methods=['PUT'])
def post():
    session_name = request.cookies.get('session')

    title = request.form.get('title')
    (env, _) = sessions.get(session_name)
    (res, new_env) = evalString(title, env)

    sessions[session_name] = (new_env, time.time())
    clean_old_sessions()

    return f"""<div class='p-2'><pre class='font-bold'>> {title}</pre>
<pre>{res}</pre></div>"""
