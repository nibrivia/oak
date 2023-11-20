from flask import Flask, request, render_template
from main import evalString

app = Flask(__name__)

@app.route("/")
def testertester():
    return render_template('index.html')

@app.route('/clicked')
def clicked():
    return "<p>Clicked</p>"

@app.route('/put', methods=['PUT'])
def post():
    title = request.form.get('title')
    return f"<pre>{evalString(title)}</pre>"
