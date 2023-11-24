from flask import Flask, request, render_template, make_response
import time
import uuid
from main import evalString, default_env, Env

app = Flask(__name__)


class SessionRegistry:
    def __init__(self):
        self.sessions = dict()

    def __getitem__(self, session_key: str) -> Env:
        self._refresh_session(session_key)
        (env, _) = self.sessions.get(session_key, (default_env, 0))

        self.sessions[session_key] = (env, time.time())
        self._clean_old_sessions()

        return env

    def _refresh_session(self, session_key: str) -> None:
        if session_key in self.sessions:
            (env, _) = self.sessions.get(session_key)
            self.sessions[session_key] = (env, time.time())

    def __setitem__(self, session_key: str, env: Env) -> None:
        self.sessions[session_key] = (env, time.time())
        self._clean_old_sessions()

    def _clean_old_sessions(self) -> None:
        keys_to_delete = []
        for session_name, (_, date_created) in self.sessions.items():
            if time.time() - date_created > 600:
                keys_to_delete.append(session_name)

        for k in keys_to_delete:
            del self.sessions[k]


session_registry = SessionRegistry()


@app.route("/")
def full_page_template():
    resp = make_response(render_template('index.html'))

    session_name = uuid.uuid4().hex
    resp.set_cookie('session', session_name)
    print(session_name)

    session_registry[session_name] = default_env

    return resp


@app.route('/put', methods=['PUT', 'OPTIONS'])
def post():
    if request.method == "OPTIONS":
        response = make_response()
        response.headers.add("Access-Control-Allow-Origin", "*")
        response.headers.add('Access-Control-Allow-Headers', "*")
        response.headers.add('Access-Control-Allow-Methods', "*")
        return response

    session_name = request.cookies.get('session')

    env = session_registry[session_name]
    command = request.form.get('title') or ""
    (res, new_env) = evalString(command, env)

    session_registry[session_name] = new_env

    response = make_response(f"""<div class='p-2'><pre class='font-bold'>> {command}</pre>
<pre>{res}</pre></div>""")
    response.headers.add("Access-Control-Allow-Origin", "*")

    return response
