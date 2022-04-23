



import os
from werkzeug.utils import secure_filename

from flask import Flask, flash, request, redirect, url_for,render_template, flash, url_for, session, redirect

import tkinter as tk
from tkinter import messagebox
from socket import *
import time, sys, threading, time, random, winsound, os
import hashlib as hasher
from hashlib import sha256
from datetime import datetime
from math import log
import time
import operator
import os
import sys
import random
import numpy
import hashlib
import string
import os
import collections
import struct
import binascii
import base64
from copy import copy
from fractions import gcd # Greatest Common Denominator
from random import SystemRandom # cryptographic random byte generator
rand=SystemRandom()
from numpy import asarray
from numpy import save
from numpy import load
from tkinter import *
from PIL import ImageTk, Image
from tkinter import filedialog
import os
from PIL import Image
from pyzbar.pyzbar import decode
import cv2
import numpy as np
import pathlib
from flask import session
import json
from web3 import Web3
from typing import NamedTuple
os.system('color B')
import json
from web3 import Web3
from typing import NamedTuple
import qrcode
from PIL import Image, ImageDraw, ImageFont
import pandas as pd
from web3.middleware import geth_poa_middleware
from flask_mysqldb import MySQL 
os.system('color B')


# Convert a string with hex digits, colons, and whitespace to a long integer
def hex2int(hexString):
	return int("".join(hexString.replace(":","").split()),16)

# Half the extended Euclidean algorithm:
#    Computes   gcd(a,b) = a*x + b*y
#    Returns only gcd, x (not y)
# From http://rosettacode.org/wiki/Modular_inverse#Python
def half_extended_gcd(aa, bb):
	lastrem, rem = abs(aa), abs(bb)
	x, lastx = 0, 1
	while rem:
		lastrem, (quotient, rem) = rem, divmod(lastrem, rem)
		x, lastx = lastx - quotient*x, x
	return lastrem, lastx

# Modular inverse: compute the multiplicative inverse i of a mod m:
#     i*a = a*i = 1 mod m
def modular_inverse(a, m):
	g, x = half_extended_gcd(a, m)
	if g != 1:
		raise ValueError
	return x % m


# An elliptic curve has these fields:
#   p: the prime used to mod all coordinates
#   a: linear part of curve: y^2 = x^3 + ax + b
#   b: constant part of curve
#   G: a curve point (G.x,G.y) used as a "generator"
#   n: the order of the generator
class ECcurve:
	def __init__(self):
		return

	# Prime field multiplication: return a*b mod p
	def field_mul(self,a,b):
		return (a*b)%self.p

	# Prime field division: return num/den mod p
	def field_div(self,num,den):
		inverse_den=modular_inverse(den%self.p,self.p)
		return self.field_mul(num%self.p,inverse_den)

	# Prime field exponentiation: raise num to power mod p
	def field_exp(self,num,power):
		return pow(num%self.p,power,self.p)

	# Return the special identity point
	#   We pick x=p, y=0
	def identity(self):
		return ECpoint(self,self.p,0,1)

	# Return true if point Q lies on our curve

	def touches(self,Q):
		x=Q.get_x()
		y=Q.get_y()
		y2=(y*y)%self.p
		x3ab=(self.field_mul((x*x)%self.p+self.a,x)+self.b)%self.p
		return y2==(x3ab)%self.p

	# Return the slope of the tangent of this curve at point Q
	def tangent(self,Q):
		return self.field_div(Q.x*Q.x*3+self.a,Q.y*2)

	# Return a doubled version of this elliptic curve point
	#  Closely follows Gueron & Krasnov 2013 figure 2
	def double(self,Q):
		if (Q.x==self.p): # doubling the identity
			return Q
		S=(4*Q.x*Q.y*Q.y)%self.p
		Z2=Q.z*Q.z
		Z4=(Z2*Z2)%self.p
		M=(3*Q.x*Q.x+self.a*Z4)
		x=(M*M-2*S)%self.p
		Y2=Q.y*Q.y
		y=(M*(S-x)-8*Y2*Y2)%self.p
		z=(2*Q.y*Q.z)%self.p
		return ECpoint(self,x,y,z)

	# Return the "sum" of these elliptic curve points
	#  Closely follows Gueron & Krasnov 2013 figure 2
	def add(self,Q1,Q2):
		# Identity special cases
		if (Q1.x==self.p): # Q1 is identity
			return Q2
		if (Q2.x==self.p): # Q2 is identity
			return Q1
		Q1z2=Q1.z*Q1.z
		Q2z2=Q2.z*Q2.z
		xs1=(Q1.x*Q2z2)%self.p
		xs2=(Q2.x*Q1z2)%self.p
		ys1=(Q1.y*Q2z2*Q2.z)%self.p
		ys2=(Q2.y*Q1z2*Q1.z)%self.p

		# Equality special cases
		if (xs1==xs2):
			if (ys1==ys2): # adding point to itself
				return self.double(Q1)
			else: # vertical pair--result is the identity
				return self.identity()

		# Ordinary case
		xd=(xs2-xs1)%self.p   # caution: if not python, negative result?
		yd=(ys2-ys1)%self.p
		xd2=(xd*xd)%self.p
		xd3=(xd2*xd)%self.p
		x=(yd*yd-xd3-2*xs1*xd2)%self.p
		y=(yd*(xs1*xd2-x)-ys1*xd3)%self.p
		z=(xd*Q1.z*Q2.z)%self.p
		return ECpoint(self,x,y,z)

	# "Multiply" this elliptic curve point Q by the scalar (integer) m
	#    Often the point Q will be the generator G
	def mul(self,m,Q):
		R=self.identity() # return point
		while m!=0:  # binary multiply loop
			if m&1: # bit is set
				#print("  mul: adding Q to R =",R);
				R=self.add(R,Q)
				#print("  mul: added Q to R =",R);
			m=m>>1
			if (m!=0):
				#print("  mul: doubling Q =",Q);
				Q=self.double(Q)

		return R



# A point on an elliptic curve: (x,y)
#   Using special (X,Y,Z) Jacobian point representation
class ECpoint:
	"""A point on an elliptic curve (x/z^2,y/z^3)"""
	def __init__(self,curve, x,y,z):
		self.curve=curve
		self.x=x
		self.y=y
		self.z=z
		# This self-check has a big performance cost.
		#if not x==curve.p and not curve.touches(self):
		#	print(" ECpoint left curve: ",self)

	# "Add" this point to another point on the same curve
	def add(self,Q2):
		return self.curve.add(self,Q2)

	# "Multiply" this point by a scalar
	def mul(self,m):
		return self.curve.mul(m,self)

	# Extract non-projective X and Y coordinates
	#   This is the only time we need the expensive modular inverse
	def get_x(self):
		return self.curve.field_div(self.x,(self.z*self.z)%self.curve.p);
	def get_y(self):
		return self.curve.field_div(self.y,(self.z*self.z*self.z)%self.curve.p);

	# Print this ECpoint
	def __str__(self):
		if (self.x==self.curve.p):
			return "identity_point"
		else:
			return "("+str(self.get_x())+", "+str(self.get_y())+")"


# This is the BitCoin elliptic curve, SECG secp256k1
#   See http://www.secg.org/SEC2-Ver-1.0.pdf
secp256k1=ECcurve()
secp256k1.p=hex2int("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F");
secp256k1.a=0 # it's a Koblitz curve, with no linear part
secp256k1.b=7

# n is the order of the curve, used for ECDSA
secp256k1.n=hex2int("FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFE BAAEDCE6 AF48A03B BFD25E8C D0364141");

# SEC's "04" means they're representing the generator point's X,Y parts explicitly.
secp256k1.G=ECpoint(curve=secp256k1,
  x = hex2int("79BE667E F9DCBBAC 55A06295 CE870B07 029BFCDB 2DCE28D9 59F2815B 16F81798"),
  y = hex2int("483ADA77 26A3C465 5DA4FBFC 0E1108A8 FD17B448 A6855419 9C47D08F FB10D4B8"),
  z = 1  # projective coordinates, start with Z==1
);

#################
# Test program:
curve=secp256k1
G=curve.G; # generator of curve
n=curve.n; # order of curve
def ECPM(pwd):
	pk=G.mul(pwd);
	return pk

def encode_public_key(P):
        x = P.get_x().to_bytes(32, "big")
        y = P.get_y().to_bytes(32, "big")
        return b"\x04" + x + y

def decode_public_key(public_key_bytes):
    left = int.from_bytes(public_key_bytes[1:33], byteorder='big')
    right = int.from_bytes(public_key_bytes[33:65], byteorder='big')
    return ECpoint(curve,x=left,y=right,z=1)







def compress_public_key(public_key):
    x, y = public_key.get_x(),public_key.get_y()
    if y % 2 == 0:
        prefix = b"\x02"
    else:
        prefix = b"\x03"
    return (prefix + x.to_bytes(32,'big')).hex()


def decompress_public_key(compressed_public_key):
    compressed_public_key_bytes=bytes.fromhex(compressed_public_key) 
    if len(compressed_public_key_bytes) != 33:
        raise ValueError("Invalid compressed public key")

    prefix = compressed_public_key_bytes[0]
    if prefix not in (2, 3):
        raise ValueError("Invalid compressed public key")

    x = int.from_bytes(compressed_public_key_bytes[1:], byteorder='big')
    y_squared = (x**3 +  7) % curve.p
    y_abs = pow(y_squared, ((curve.p + 1) // 4), curve.p)

    if (prefix == 2 and y_abs & 1 == 1) or (prefix == 3 and y_abs & 1 == 0):
        y = (-y_abs) % curve.p
    else:
        y = y_abs

    return ECpoint(curve,x,y,z=1)

def sign(pwd, msg):
	mhash=msg.hex();
	z=int(mhash,16);
	k=rand.getrandbits(256)%n; # message nonce
	C=G.mul(k);
	r=C.get_x()%n; # part 1 of signature
	s=(((z+r*pwd)%n)*modular_inverse(k,n))%n; # part 2 of signature
	r=r.to_bytes(32,'big').hex()
	s=s.to_bytes(32,'big').hex()
	sig =r+s
	return sig

def verify(pk, msg,sig):
	mhash=msg.hex();

	z1=int(mhash,16);
	r=int.from_bytes(bytes.fromhex(sig[:64]),byteorder='big')
	s=int.from_bytes(bytes.fromhex(sig[64:]),byteorder='big')
	si=modular_inverse(s,n) # =1/s
	u1=(z1*si)%n  # u1=z/s mod n
	u2=(r*si)%n  # u2=r/s mod n
	C=G.mul(u1).add(pk.mul(u2)); # C = u1 G + u2 Q
	return (r%n==C.get_x()%n)

def hash_sha256(data):
    m= hashlib.sha256()
    m.update(data.encode('UTF'))
    return m.hexdigest()




def Generate_certificate(data,QR):
    font = ImageFont.truetype('arial.ttf',40)
    filepath = os.path.join(app.config['UPLOAD_FOLDER'], 'KU.png')
    img = Image.open(filepath)
    draw = ImageDraw.Draw(img)
    a=data[0]
    b="Affliation: "+data[3]
    c="Full Name: "+data[4]
    d="Project Title: "+data[2]
    e="Project Reg. Number: "+data[1]
    f="Earned Score: "+data[6]
    g=data[7]
    h=data[5]+", Professor"


    draw.text(xy=(300,260),text='{}'.format(a),fill=(0,0,0),font=font)
    draw.text(xy=(520,760),text='{}'.format(b),fill=(0,0,0),font=font)
    draw.text(xy=(520,820),text='{}'.format(c),fill=(0,0,0),font=font)
    draw.text(xy=(520,880),text='{}'.format(d),fill=(0,0,0),font=font)
    draw.text(xy=(520,940),text='{}'.format(e),fill=(0,0,0),font=font)
    draw.text(xy=(520,1000),text='{}'.format(f),fill=(0,0,0),font=font)
    draw.text(xy=(750,1600),text='{}'.format(g),fill=(0,0,0),font=font)
    draw.text(xy=(680,1800),text='{}'.format(h),fill=(0,0,0),font=font)
    draw.text(xy=(430,1300),text='{}'.format("Awarded by the Department of Computer Science"),fill=(0,0,0),font=font)
    draw.text(xy=(550,1360),text='{}'.format("and Engineering, Korea University"),fill=(0,0,0),font=font)

    baseheight =200
    hpercent = (baseheight / float(QR.size[1]))
    wsize = int((float(QR.size[0]) * float(hpercent)))
    QR = QR.resize((wsize, baseheight), Image.ANTIALIAS)

    back_im = img.copy()
    back_im.paste(QR,(380, 1700))
    path=os.path.join(app.config['UPLOAD_FOLDER'], str(data[0])+'.png')
    back_im.save(path)

    # with open(path, 'rb') as file:
        # binaryData = file.read()
    # cur = mysql.connection.cursor()
    # # cur.execute('''CREATE TABLE certificate (cid INTEGER, image LONGBLOB)''')
    # sql_insert_blob_query = """ INSERT INTO certificate
                          # (cid, image) VALUES (%s,%s)"""
    # # Convert data into tuple format
    # insert_blob_tuple = (data[0], binaryData)
    # cur.execute(sql_insert_blob_query, insert_blob_tuple)
    # # cur.execute('''INSERT INTO certificate VALUES (1, image)''')
    # # cur.execute('''INSERT INTO example VALUES (2, 'Billy')''')
    # mysql.connection.commit()


        



def cert_verification(filepath,filename):
    # img = Image.open(x)
    # img = img.resize((250, 250), Image.ANTIALIAS)
    # img = ImageTk.PhotoImage(img)
    # panel = Label(root, image=img)
    # panel.image = img
    # panel.pack()
    # Load imgae, grayscale, Gaussian blur, Otsu's threshold
    image = cv2.imread(filepath)
    original = image.copy()
    gray = cv2.cvtColor(image, cv2.COLOR_BGR2GRAY)
    blur = cv2.GaussianBlur(gray, (9,9), 0)
    thresh = cv2.threshold(blur, 0, 255, cv2.THRESH_BINARY_INV + cv2.THRESH_OTSU)[1]

    # Morph close
    kernel = cv2.getStructuringElement(cv2.MORPH_RECT, (5,5))
    close = cv2.morphologyEx(thresh, cv2.MORPH_CLOSE, kernel, iterations=2)

    # Find contours and filter for QR code
    cnts = cv2.findContours(close, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
    cnts = cnts[0] if len(cnts) == 2 else cnts[1]
    ROI=[]
    for c in cnts:
        peri = cv2.arcLength(c, True)
        approx = cv2.approxPolyDP(c, 0.04 * peri, True)
        x,y,w,h = cv2.boundingRect(approx)
        area = cv2.contourArea(c)
        ar = w / float(h)
        if len(approx) == 4 and area > 1000 and (ar > .85 and ar < 1.3):
            cv2.rectangle(image, (x, y), (x + w, y + h), (36,255,12), 3)
            ROI = original[y:y+h, x:x+w]
            path1=os.path.join(app.config['UPLOAD_FOLDER'], 'ROI-'+filename)
            cv2.imwrite(path1, ROI)
    # cv2.imshow('thresh', thresh)
    # cv2.imshow('close', close)
    # cv2.imshow('ROI', ROI)
    # cv2.waitKey()
    validity=''
    IM = decode(original)
    if len(ROI)!=0:
        QR = decode(ROI)
        if len(QR)!=0:
            QR_data = QR[0][0].decode()
            try:
                if len(eval(QR_data))==3 and len(eval(QR_data)[0])==8:
                    cdata=eval(QR_data)[0]
                    pfhash=contract2.functions.getCertificateInfo(str(eval(QR_data)[0][0])).call()[2].hex()
                    if hash_sha256(str(cdata))==pfhash and verify(decompress_public_key(eval(QR_data)[2]),bytes.fromhex(pfhash),eval(QR_data)[1]):
                        validity= "True"
                    else:
                        validity= "False"  
                else:
                    validity="Invalid certificate"
            except Exception:
                validity="False"
                pass

        elif len(IM)!=0:
            QR_data = IM[0][0].decode()
            try:
                if len(eval(QR_data))==3 and len(eval(QR_data)[0])==8:
                    cdata=eval(QR_data)[0]
                    pfhash=contract2.functions.getCertificateInfo(str(eval(QR_data)[0][0])).call()[2].hex()
                    if hash_sha256(str(cdata))==pfhash and verify(decompress_public_key(eval(QR_data)[2]),bytes.fromhex(pfhash),eval(QR_data)[1]):
                        validity= "True"
                    else:
                        validity= "False"  
                else:
                    validity="Invalid certificate"
            except Exception:
                validity="False"
                pass
        else:
            validity="No QR code detected"
    else:
        if len(IM)!=0:
            QR_data = IM[0][0].decode()
            try:
                if len(eval(QR_data))==3 and len(eval(QR_data)[0])==8:
                    cdata=eval(QR_data)[0]
                    pfhash=contract2.functions.getCertificateInfo(str(eval(QR_data)[0][0])).call()[2].hex()
                    if hash_sha256(str(cdata))==pfhash and verify(decompress_public_key(eval(QR_data)[2]),bytes.fromhex(pfhash),eval(QR_data)[1]):
                        validity= "True"
                    else:
                        validity= "False"  
                else:
                    validity="Invalid certificate"
            except Exception:
                validity="False"
                pass
        else:
            validity="No QR code detected"
    # if validity=="True":
        # image = cv2.copyMakeBorder(image, 100, 100, 100, 100, cv2.BORDER_CONSTANT,value=[36,255,12])
    # else:
        # image = cv2.copyMakeBorder(image, 100, 100, 100, 100, cv2.BORDER_CONSTANT,value=[0,0,255])

    path2=os.path.join(app.config['UPLOAD_FOLDER'], 'C-'+filename)
    cv2.imwrite(path2, image)
    return(path2,validity)

app = Flask(__name__)
# sess = Session()







app = Flask(__name__)
UPLOAD_FOLDER = 'static/uploads/'
ALLOWED_EXTENSIONS = set(['txt', 'pdf', 'png', 'jpg', 'jpeg', 'gif', 'log'])
app.config['UPLOAD_FOLDER'] = UPLOAD_FOLDER

app.config['MYSQL_USER'] = 'admin'
app.config['MYSQL_PASSWORD'] = 'hancomwith12!@'
app.config['MYSQL_HOST'] = '1.237.174.101'
app.config['MYSQL_DB'] = 'ricardian'
app.config['MYSQL_CURSORCLASS'] = 'DictCursor'

mysql = MySQL(app)
@app.route('/',methods=['GET', 'POST'])
def registration():
    result = {
            'pf_no' : '',    
            'pf_name' : '',
            'reg_dtime' : '',
            'reg_name' : '',
            'professor_name' : '',
            'score' : 0,

    }
    return render_template('registration.html',result=result)
    
@app.route('/inquiry',methods=['GET', 'POST'])
def inquiry():
    result = {
            'pf_no' : '',    
            'pf_name' : '',
            'reg_dtime' : '',
            'reg_name' : '',
            'professor_name' : '',
            'score' : 0,

    }
    return render_template('inquiry.html',result=result)

@app.route('/certificate',methods=['GET', 'POST'])    
def certificate():
    return render_template('certificate.html',result=0,filepath='')
    
            
@app.route('/getCertificate', methods=['GET', 'POST'])
def getCertificate():
    try:
        if contract2.functions.getCertificateInfo(request.form['cert_no']).call()[0]:
            result=1
            path = os.path.join(app.config['UPLOAD_FOLDER'], request.form['cert_no']+".png")
        else:
            result=2
            path=''
    except Exception:
        result = 2 
        path=''  
    return render_template('certificate.html',result=result,filepath=path)


@app.route('/verification', methods=['GET', 'POST'])
def verification():
    result = {
            'result' : '',    
            'error' : '',}    
    return render_template('verification.html',result='',filepath='')
  

def allowed_file(filename):
    return '.' in filename and \
        filename.rsplit('.', 1)[1].lower() in ALLOWED_EXTENSIONS

@app.route('/upload_file', methods=['POST'])
def upload_file():
    
    # check if the post request has the file part
    if 'file' not in request.files:        
        result = {
            'result' : 0,    
            'error' : 'File not available',
        }
        return render_template('verification.html', result=result)
    
    file = request.files['file']
    
    # if user does not select file, browser also
    # submit an empty part without filename
    if file.filename == '':        
        result = {
            'result' : 0,    
            'error' : 'File not available',
        }
        return render_template('verification.html', result=result)
    
    if file and allowed_file(file.filename):
        filename = secure_filename(file.filename)
        filepath = os.path.join(app.config['UPLOAD_FOLDER'], filename)
        file.save(filepath)
        
        result = {
            'result' : 1,
            'error' : '0',
            'image_location' : filepath
        }
        return render_template('verification.html', result = result, filepath =cert_verification(filepath,filename))
    
    #return content
    return render_template('verification.html', result=result)

# Set up web3 connection with Quorum
quorum_url = "http://163.152.161.203:7545"
web3 = Web3(Web3.HTTPProvider(quorum_url))
web3.middleware_onion.inject(geth_poa_middleware, layer=0)
# # set pre-funded account as sender
web3.eth.defaultAccount = Web3.toChecksumAddress('0x0b36b1E560E90b96f2e6E6bdd77c1bE2e9Ab90E9')
print(web3.isConnected())
private_key=hex2int("bfeb34154e07a6ffd7f56b16250f6a9942ada6a472ee841e6621872406637142")
public_key=bytes.fromhex(compress_public_key(ECPM(private_key)))
def deployPortfolioManager():
    abi=json.loads('[{"anonymous":false,"inputs":[{"indexed":false,"internalType":"string","name":"_pf_no","type":"string"},{"indexed":false,"internalType":"string","name":"_reg_name","type":"string"},{"indexed":false,"internalType":"string","name":"_professor_name","type":"string"}],"name":"newPortfolioCreated","type":"event"},{"anonymous":false,"inputs":[{"indexed":false,"internalType":"string","name":"_cert_no","type":"string"},{"indexed":false,"internalType":"string","name":"_pf_no","type":"string"},{"indexed":false,"internalType":"string","name":"_reg_name","type":"string"},{"indexed":false,"internalType":"string","name":"_professor_name","type":"string"},{"indexed":false,"internalType":"uint256","name":"_score","type":"uint256"}],"name":"pf_CertificateIssued","type":"event"},{"inputs":[{"internalType":"uint256","name":"","type":"uint256"}],"name":"PortfolioList","outputs":[{"internalType":"string","name":"","type":"string"}],"stateMutability":"view","type":"function"},{"inputs":[],"name":"countPortfolio","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"stateMutability":"view","type":"function"},{"inputs":[{"internalType":"string","name":"_pf_no","type":"string"}],"name":"getPortfolioInfo","outputs":[{"internalType":"string","name":"","type":"string"},{"internalType":"string","name":"","type":"string"},{"internalType":"string","name":"","type":"string"},{"internalType":"string","name":"","type":"string"},{"internalType":"string","name":"","type":"string"},{"internalType":"bytes","name":"","type":"bytes"},{"internalType":"uint256","name":"","type":"uint256"}],"stateMutability":"view","type":"function"},{"inputs":[{"internalType":"string","name":"_pf_no","type":"string"}],"name":"getPortfolioStatus","outputs":[{"internalType":"string","name":"","type":"string"}],"stateMutability":"view","type":"function"},{"inputs":[{"internalType":"string","name":"_pf_no","type":"string"}],"name":"getPortfolioURL","outputs":[{"internalType":"string","name":"","type":"string"}],"stateMutability":"view","type":"function"},{"inputs":[{"internalType":"string","name":"_pf_no","type":"string"},{"internalType":"string","name":"_pf_name","type":"string"},{"internalType":"string","name":"_reg_dtime","type":"string"},{"internalType":"string","name":"_reg_name","type":"string"},{"internalType":"string","name":"_professor_name","type":"string"},{"internalType":"bytes","name":"_professor_pk","type":"bytes"},{"internalType":"uint256","name":"_score","type":"uint256"},{"internalType":"string","name":"_pf_status","type":"string"},{"internalType":"string","name":"_pf_url","type":"string"}],"name":"newPortfolio","outputs":[],"stateMutability":"nonpayable","type":"function"}]');
    bytecode = "0x608060405234801561001057600080fd5b50611d1c806100206000396000f3fe608060405234801561001057600080fd5b50600436106100625760003560e01c80636ac773dc146100675780637602cda91461054e5780638ae50d8c14610682578063d6a71974146107b6578063ec77f8301461085d578063fa3118d51461087b575b600080fd5b61054c600480360361012081101561007e57600080fd5b810190808035906020019064010000000081111561009b57600080fd5b8201836020820111156100ad57600080fd5b803590602001918460018302840111640100000000831117156100cf57600080fd5b91908080601f016020809104026020016040519081016040528093929190818152602001838380828437600081840152601f19601f8201169050808301925050505050505091929192908035906020019064010000000081111561013257600080fd5b82018360208201111561014457600080fd5b8035906020019184600183028401116401000000008311171561016657600080fd5b91908080601f016020809104026020016040519081016040528093929190818152602001838380828437600081840152601f19601f820116905080830192505050505050509192919290803590602001906401000000008111156101c957600080fd5b8201836020820111156101db57600080fd5b803590602001918460018302840111640100000000831117156101fd57600080fd5b91908080601f016020809104026020016040519081016040528093929190818152602001838380828437600081840152601f19601f8201169050808301925050505050505091929192908035906020019064010000000081111561026057600080fd5b82018360208201111561027257600080fd5b8035906020019184600183028401116401000000008311171561029457600080fd5b91908080601f016020809104026020016040519081016040528093929190818152602001838380828437600081840152601f19601f820116905080830192505050505050509192919290803590602001906401000000008111156102f757600080fd5b82018360208201111561030957600080fd5b8035906020019184600183028401116401000000008311171561032b57600080fd5b91908080601f016020809104026020016040519081016040528093929190818152602001838380828437600081840152601f19601f8201169050808301925050505050505091929192908035906020019064010000000081111561038e57600080fd5b8201836020820111156103a057600080fd5b803590602001918460018302840111640100000000831117156103c257600080fd5b91908080601f016020809104026020016040519081016040528093929190818152602001838380828437600081840152601f19601f820116905080830192505050505050509192919290803590602001909291908035906020019064010000000081111561042f57600080fd5b82018360208201111561044157600080fd5b8035906020019184600183028401116401000000008311171561046357600080fd5b91908080601f016020809104026020016040519081016040528093929190818152602001838380828437600081840152601f19601f820116905080830192505050505050509192919290803590602001906401000000008111156104c657600080fd5b8201836020820111156104d857600080fd5b803590602001918460018302840111640100000000831117156104fa57600080fd5b91908080601f016020809104026020016040519081016040528093929190818152602001838380828437600081840152601f19601f820116905080830192505050505050509192919290505050610bd2565b005b6106076004803603602081101561056457600080fd5b810190808035906020019064010000000081111561058157600080fd5b82018360208201111561059357600080fd5b803590602001918460018302840111640100000000831117156105b557600080fd5b91908080601f016020809104026020016040519081016040528093929190818152602001838380828437600081840152601f19601f820116905080830192505050505050509192919290505050611208565b6040518080602001828103825283818151815260200191508051906020019080838360005b8381101561064757808201518184015260208101905061062c565b50505050905090810190601f1680156106745780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b61073b6004803603602081101561069857600080fd5b81019080803590602001906401000000008111156106b557600080fd5b8201836020820111156106c757600080fd5b803590602001918460018302840111640100000000831117156106e957600080fd5b91908080601f016020809104026020016040519081016040528093929190818152602001838380828437600081840152601f19601f820116905080830192505050505050509192919290505050611316565b6040518080602001828103825283818151815260200191508051906020019080838360005b8381101561077b578082015181840152602081019050610760565b50505050905090810190601f1680156107a85780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b6107e2600480360360208110156107cc57600080fd5b8101908080359060200190929190505050611424565b6040518080602001828103825283818151815260200191508051906020019080838360005b83811015610822578082015181840152602081019050610807565b50505050905090810190601f16801561084f5780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b6108656114e0565b6040518082815260200191505060405180910390f35b6109346004803603602081101561089157600080fd5b81019080803590602001906401000000008111156108ae57600080fd5b8201836020820111156108c057600080fd5b803590602001918460018302840111640100000000831117156108e257600080fd5b91908080601f016020809104026020016040519081016040528093929190818152602001838380828437600081840152601f19601f8201169050808301925050505050505091929192905050506114ed565b6040518080602001806020018060200180602001806020018060200188815260200187810387528e818151815260200191508051906020019080838360005b8381101561098e578082015181840152602081019050610973565b50505050905090810190601f1680156109bb5780820380516001836020036101000a031916815260200191505b5087810386528d818151815260200191508051906020019080838360005b838110156109f45780820151818401526020810190506109d9565b50505050905090810190601f168015610a215780820380516001836020036101000a031916815260200191505b5087810385528c818151815260200191508051906020019080838360005b83811015610a5a578082015181840152602081019050610a3f565b50505050905090810190601f168015610a875780820380516001836020036101000a031916815260200191505b5087810384528b818151815260200191508051906020019080838360005b83811015610ac0578082015181840152602081019050610aa5565b50505050905090810190601f168015610aed5780820380516001836020036101000a031916815260200191505b5087810383528a818151815260200191508051906020019080838360005b83811015610b26578082015181840152602081019050610b0b565b50505050905090810190601f168015610b535780820380516001836020036101000a031916815260200191505b50878103825289818151815260200191508051906020019080838360005b83811015610b8c578082015181840152602081019050610b71565b50505050905090810190601f168015610bb95780820380516001836020036101000a031916815260200191505b509d505050505050505050505050505060405180910390f35b8860008a6040518082805190602001908083835b60208310610c095780518252602082019150602081019050602083039250610be6565b6001836020036101000a03801982511681845116808217855250505050505090500191505090815260200160405180910390206000019080519060200190610c52929190611bad565b508760008a6040518082805190602001908083835b60208310610c8a5780518252602082019150602081019050602083039250610c67565b6001836020036101000a03801982511681845116808217855250505050505090500191505090815260200160405180910390206001019080519060200190610cd3929190611bad565b508660008a6040518082805190602001908083835b60208310610d0b5780518252602082019150602081019050602083039250610ce8565b6001836020036101000a03801982511681845116808217855250505050505090500191505090815260200160405180910390206002019080519060200190610d54929190611bad565b508560008a6040518082805190602001908083835b60208310610d8c5780518252602082019150602081019050602083039250610d69565b6001836020036101000a03801982511681845116808217855250505050505090500191505090815260200160405180910390206003019080519060200190610dd5929190611bad565b508460008a6040518082805190602001908083835b60208310610e0d5780518252602082019150602081019050602083039250610dea565b6001836020036101000a03801982511681845116808217855250505050505090500191505090815260200160405180910390206004019080519060200190610e56929190611bad565b508360008a6040518082805190602001908083835b60208310610e8e5780518252602082019150602081019050602083039250610e6b565b6001836020036101000a03801982511681845116808217855250505050505090500191505090815260200160405180910390206005019080519060200190610ed7929190611c3b565b508260008a6040518082805190602001908083835b60208310610f0f5780518252602082019150602081019050602083039250610eec565b6001836020036101000a0380198251168184511680821785525050505050509050019150509081526020016040518091039020600601819055508160008a6040518082805190602001908083835b60208310610f805780518252602082019150602081019050602083039250610f5d565b6001836020036101000a03801982511681845116808217855250505050505090500191505090815260200160405180910390206007019080519060200190610fc9929190611bad565b508060008a6040518082805190602001908083835b602083106110015780518252602082019150602081019050602083039250610fde565b6001836020036101000a0380198251168184511680821785525050505050509050019150509081526020016040518091039020600801908051906020019061104a929190611bad565b50600189908060018154018082558091505060019003906000526020600020016000909190919091509080519060200190611086929190611bad565b507f940c345badda4e20e0698f32204fb8deb81328c15b449fbca415fb536c17e3fa89878760405180806020018060200180602001848103845287818151815260200191508051906020019080838360005b838110156110f35780820151818401526020810190506110d8565b50505050905090810190601f1680156111205780820380516001836020036101000a031916815260200191505b50848103835286818151815260200191508051906020019080838360005b8381101561115957808201518184015260208101905061113e565b50505050905090810190601f1680156111865780820380516001836020036101000a031916815260200191505b50848103825285818151815260200191508051906020019080838360005b838110156111bf5780820151818401526020810190506111a4565b50505050905090810190601f1680156111ec5780820380516001836020036101000a031916815260200191505b50965050505050505060405180910390a1505050505050505050565b60606000826040518082805190602001908083835b60208310611240578051825260208201915060208101905060208303925061121d565b6001836020036101000a03801982511681845116808217855250505050505090500191505090815260200160405180910390206007018054600181600116156101000203166002900480601f01602080910402602001604051908101604052809291908181526020018280546001816001161561010002031660029004801561130a5780601f106112df5761010080835404028352916020019161130a565b820191906000526020600020905b8154815290600101906020018083116112ed57829003601f168201915b50505050509050919050565b60606000826040518082805190602001908083835b6020831061134e578051825260208201915060208101905060208303925061132b565b6001836020036101000a03801982511681845116808217855250505050505090500191505090815260200160405180910390206008018054600181600116156101000203166002900480601f0160208091040260200160405190810160405280929190818152602001828054600181600116156101000203166002900480156114185780601f106113ed57610100808354040283529160200191611418565b820191906000526020600020905b8154815290600101906020018083116113fb57829003601f168201915b50505050509050919050565b6001818154811061143457600080fd5b906000526020600020016000915090508054600181600116156101000203166002900480601f0160208091040260200160405190810160405280929190818152602001828054600181600116156101000203166002900480156114d85780601f106114ad576101008083540402835291602001916114d8565b820191906000526020600020905b8154815290600101906020018083116114bb57829003601f168201915b505050505081565b6000600180549050905090565b606080606080606080600080886040518082805190602001908083835b6020831061152d578051825260208201915060208101905060208303925061150a565b6001836020036101000a03801982511681845116808217855250505050505090500191505090815260200160405180910390206000016000896040518082805190602001908083835b602083106115995780518252602082019150602081019050602083039250611576565b6001836020036101000a038019825116818451168082178552505050505050905001915050908152602001604051809103902060010160008a6040518082805190602001908083835b6020831061160557805182526020820191506020810190506020830392506115e2565b6001836020036101000a038019825116818451168082178552505050505050905001915050908152602001604051809103902060020160008b6040518082805190602001908083835b60208310611671578051825260208201915060208101905060208303925061164e565b6001836020036101000a038019825116818451168082178552505050505050905001915050908152602001604051809103902060030160008c6040518082805190602001908083835b602083106116dd57805182526020820191506020810190506020830392506116ba565b6001836020036101000a038019825116818451168082178552505050505050905001915050908152602001604051809103902060040160008d6040518082805190602001908083835b602083106117495780518252602082019150602081019050602083039250611726565b6001836020036101000a038019825116818451168082178552505050505050905001915050908152602001604051809103902060050160008e6040518082805190602001908083835b602083106117b55780518252602082019150602081019050602083039250611792565b6001836020036101000a038019825116818451168082178552505050505050905001915050908152602001604051809103902060060154868054600181600116156101000203166002900480601f0160208091040260200160405190810160405280929190818152602001828054600181600116156101000203166002900480156118815780601f1061185657610100808354040283529160200191611881565b820191906000526020600020905b81548152906001019060200180831161186457829003601f168201915b50505050509650858054600181600116156101000203166002900480601f01602080910402602001604051908101604052809291908181526020018280546001816001161561010002031660029004801561191d5780601f106118f25761010080835404028352916020019161191d565b820191906000526020600020905b81548152906001019060200180831161190057829003601f168201915b50505050509550848054600181600116156101000203166002900480601f0160208091040260200160405190810160405280929190818152602001828054600181600116156101000203166002900480156119b95780601f1061198e576101008083540402835291602001916119b9565b820191906000526020600020905b81548152906001019060200180831161199c57829003601f168201915b50505050509450838054600181600116156101000203166002900480601f016020809104026020016040519081016040528092919081815260200182805460018160011615610100020316600290048015611a555780601f10611a2a57610100808354040283529160200191611a55565b820191906000526020600020905b815481529060010190602001808311611a3857829003601f168201915b50505050509350828054600181600116156101000203166002900480601f016020809104026020016040519081016040528092919081815260200182805460018160011615610100020316600290048015611af15780601f10611ac657610100808354040283529160200191611af1565b820191906000526020600020905b815481529060010190602001808311611ad457829003601f168201915b50505050509250818054600181600116156101000203166002900480601f016020809104026020016040519081016040528092919081815260200182805460018160011615610100020316600290048015611b8d5780601f10611b6257610100808354040283529160200191611b8d565b820191906000526020600020905b815481529060010190602001808311611b7057829003601f168201915b505050505091509650965096509650965096509650919395979092949650565b828054600181600116156101000203166002900490600052602060002090601f016020900481019282611be35760008555611c2a565b82601f10611bfc57805160ff1916838001178555611c2a565b82800160010185558215611c2a579182015b82811115611c29578251825591602001919060010190611c0e565b5b509050611c379190611cc9565b5090565b828054600181600116156101000203166002900490600052602060002090601f016020900481019282611c715760008555611cb8565b82601f10611c8a57805160ff1916838001178555611cb8565b82800160010185558215611cb8579182015b82811115611cb7578251825591602001919060010190611c9c565b5b509050611cc59190611cc9565b5090565b5b80821115611ce2576000816000905550600101611cca565b509056fea2646970667358221220721d1a71334f90ed64b2f76fc6372ca730619d8a348fc0999c7d8f478cd09e4f64736f6c63430007040033";
    # # Instantiate and deploy contract
    Greeter = web3.eth.contract(abi=abi, bytecode=bytecode)
    # # Submit the transaction that deploys the contract
    tx_hash = Greeter.constructor().transact()
    # # Wait for the transaction to be mined, and get the transaction receipt
    tx_receipt = web3.eth.waitForTransactionReceipt(tx_hash)
    print("Portfolio is deployed at: ",tx_receipt.contractAddress)
def deployCertificateManager():
    abi=json.loads('[{"anonymous":false,"inputs":[{"indexed":false,"internalType":"string","name":"_cert_no","type":"string"},{"indexed":false,"internalType":"string","name":"_pf_no","type":"string"},{"indexed":false,"internalType":"bytes","name":"_professor_pk","type":"bytes"},{"indexed":false,"internalType":"bytes","name":"_cert_signature","type":"bytes"}],"name":"pf_CertificateIssued","type":"event"},{"inputs":[{"internalType":"uint256","name":"","type":"uint256"}],"name":"Portfolio_eCertList","outputs":[{"internalType":"string","name":"","type":"string"}],"stateMutability":"view","type":"function"},{"inputs":[],"name":"countPortfolioCerts","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"stateMutability":"view","type":"function"},{"inputs":[{"internalType":"string","name":"_cert_no","type":"string"}],"name":"getCertificateInfo","outputs":[{"internalType":"string","name":"","type":"string"},{"internalType":"string","name":"","type":"string"},{"internalType":"bytes","name":"","type":"bytes"},{"internalType":"bytes","name":"","type":"bytes"},{"internalType":"bytes","name":"","type":"bytes"}],"stateMutability":"view","type":"function"},{"inputs":[{"internalType":"string","name":"_cert_no","type":"string"},{"internalType":"string","name":"_pf_no","type":"string"},{"internalType":"string","name":"_organizationID","type":"string"},{"internalType":"bytes","name":"_pf_hash","type":"bytes"},{"internalType":"bytes","name":"_cert_signature","type":"bytes"},{"internalType":"bytes","name":"_professor_pk","type":"bytes"}],"name":"issuePortfolioCertificate","outputs":[],"stateMutability":"nonpayable","type":"function"}]');
    bytecode = "0x608060405234801561001057600080fd5b506113cf806100206000396000f3fe608060405234801561001057600080fd5b506004361061004c5760003560e01c806307dcb9f61461005157806319758ffd1461006f5780633cd145bf14610116578063507dce19146104c4575b600080fd5b6100596107a8565b6040518082815260200191505060405180910390f35b61009b6004803603602081101561008557600080fd5b81019080803590602001909291905050506107b5565b6040518080602001828103825283818151815260200191508051906020019080838360005b838110156100db5780820151818401526020810190506100c0565b50505050905090810190601f1680156101085780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b6104c2600480360360c081101561012c57600080fd5b810190808035906020019064010000000081111561014957600080fd5b82018360208201111561015b57600080fd5b8035906020019184600183028401116401000000008311171561017d57600080fd5b91908080601f016020809104026020016040519081016040528093929190818152602001838380828437600081840152601f19601f820116905080830192505050505050509192919290803590602001906401000000008111156101e057600080fd5b8201836020820111156101f257600080fd5b8035906020019184600183028401116401000000008311171561021457600080fd5b91908080601f016020809104026020016040519081016040528093929190818152602001838380828437600081840152601f19601f8201169050808301925050505050505091929192908035906020019064010000000081111561027757600080fd5b82018360208201111561028957600080fd5b803590602001918460018302840111640100000000831117156102ab57600080fd5b91908080601f016020809104026020016040519081016040528093929190818152602001838380828437600081840152601f19601f8201169050808301925050505050505091929192908035906020019064010000000081111561030e57600080fd5b82018360208201111561032057600080fd5b8035906020019184600183028401116401000000008311171561034257600080fd5b91908080601f016020809104026020016040519081016040528093929190818152602001838380828437600081840152601f19601f820116905080830192505050505050509192919290803590602001906401000000008111156103a557600080fd5b8201836020820111156103b757600080fd5b803590602001918460018302840111640100000000831117156103d957600080fd5b91908080601f016020809104026020016040519081016040528093929190818152602001838380828437600081840152601f19601f8201169050808301925050505050505091929192908035906020019064010000000081111561043c57600080fd5b82018360208201111561044e57600080fd5b8035906020019184600183028401116401000000008311171561047057600080fd5b91908080601f016020809104026020016040519081016040528093929190818152602001838380828437600081840152601f19601f820116905080830192505050505050509192919290505050610871565b005b61057d600480360360208110156104da57600080fd5b81019080803590602001906401000000008111156104f757600080fd5b82018360208201111561050957600080fd5b8035906020019184600183028401116401000000008311171561052b57600080fd5b91908080601f016020809104026020016040519081016040528093929190818152602001838380828437600081840152601f19601f820116905080830192505050505050509192919290505050610d1d565b60405180806020018060200180602001806020018060200186810386528b818151815260200191508051906020019080838360005b838110156105cd5780820151818401526020810190506105b2565b50505050905090810190601f1680156105fa5780820380516001836020036101000a031916815260200191505b5086810385528a818151815260200191508051906020019080838360005b83811015610633578082015181840152602081019050610618565b50505050905090810190601f1680156106605780820380516001836020036101000a031916815260200191505b50868103845289818151815260200191508051906020019080838360005b8381101561069957808201518184015260208101905061067e565b50505050905090810190601f1680156106c65780820380516001836020036101000a031916815260200191505b50868103835288818151815260200191508051906020019080838360005b838110156106ff5780820151818401526020810190506106e4565b50505050905090810190601f16801561072c5780820380516001836020036101000a031916815260200191505b50868103825287818151815260200191508051906020019080838360005b8381101561076557808201518184015260208101905061074a565b50505050905090810190601f1680156107925780820380516001836020036101000a031916815260200191505b509a505050505050505050505060405180910390f35b6000600180549050905090565b600181815481106107c557600080fd5b906000526020600020016000915090508054600181600116156101000203166002900480601f0160208091040260200160405190810160405280929190818152602001828054600181600116156101000203166002900480156108695780601f1061083e57610100808354040283529160200191610869565b820191906000526020600020905b81548152906001019060200180831161084c57829003601f168201915b505050505081565b846000876040518082805190602001908083835b602083106108a85780518252602082019150602081019050602083039250610885565b6001836020036101000a038019825116818451168082178552505050505050905001915050908152602001604051809103902060010190805190602001906108f1929190611260565b50836000876040518082805190602001908083835b602083106109295780518252602082019150602081019050602083039250610906565b6001836020036101000a03801982511681845116808217855250505050505090500191505090815260200160405180910390206002019080519060200190610972929190611260565b50826000876040518082805190602001908083835b602083106109aa5780518252602082019150602081019050602083039250610987565b6001836020036101000a038019825116818451168082178552505050505050905001915050908152602001604051809103902060030190805190602001906109f39291906112ee565b50816000876040518082805190602001908083835b60208310610a2b5780518252602082019150602081019050602083039250610a08565b6001836020036101000a03801982511681845116808217855250505050505090500191505090815260200160405180910390206004019080519060200190610a749291906112ee565b50806000876040518082805190602001908083835b60208310610aac5780518252602082019150602081019050602083039250610a89565b6001836020036101000a03801982511681845116808217855250505050505090500191505090815260200160405180910390206005019080519060200190610af59291906112ee565b50600186908060018154018082558091505060019003906000526020600020016000909190919091509080519060200190610b31929190611260565b507f5c27521803d35ebe8da31e95c5c44fed2ed0c85aeb8bd3c86b3b275adefa8d0e868683856040518080602001806020018060200180602001858103855289818151815260200191508051906020019080838360005b83811015610ba3578082015181840152602081019050610b88565b50505050905090810190601f168015610bd05780820380516001836020036101000a031916815260200191505b50858103845288818151815260200191508051906020019080838360005b83811015610c09578082015181840152602081019050610bee565b50505050905090810190601f168015610c365780820380516001836020036101000a031916815260200191505b50858103835287818151815260200191508051906020019080838360005b83811015610c6f578082015181840152602081019050610c54565b50505050905090810190601f168015610c9c5780820380516001836020036101000a031916815260200191505b50858103825286818151815260200191508051906020019080838360005b83811015610cd5578082015181840152602081019050610cba565b50505050905090810190601f168015610d025780820380516001836020036101000a031916815260200191505b509850505050505050505060405180910390a1505050505050565b60608060608060606000866040518082805190602001908083835b60208310610d5b5780518252602082019150602081019050602083039250610d38565b6001836020036101000a03801982511681845116808217855250505050505090500191505090815260200160405180910390206001016000876040518082805190602001908083835b60208310610dc75780518252602082019150602081019050602083039250610da4565b6001836020036101000a03801982511681845116808217855250505050505090500191505090815260200160405180910390206002016000886040518082805190602001908083835b60208310610e335780518252602082019150602081019050602083039250610e10565b6001836020036101000a03801982511681845116808217855250505050505090500191505090815260200160405180910390206003016000896040518082805190602001908083835b60208310610e9f5780518252602082019150602081019050602083039250610e7c565b6001836020036101000a038019825116818451168082178552505050505050905001915050908152602001604051809103902060040160008a6040518082805190602001908083835b60208310610f0b5780518252602082019150602081019050602083039250610ee8565b6001836020036101000a0380198251168184511680821785525050505050509050019150509081526020016040518091039020600501848054600181600116156101000203166002900480601f016020809104026020016040519081016040528092919081815260200182805460018160011615610100020316600290048015610fd65780601f10610fab57610100808354040283529160200191610fd6565b820191906000526020600020905b815481529060010190602001808311610fb957829003601f168201915b50505050509450838054600181600116156101000203166002900480601f0160208091040260200160405190810160405280929190818152602001828054600181600116156101000203166002900480156110725780601f1061104757610100808354040283529160200191611072565b820191906000526020600020905b81548152906001019060200180831161105557829003601f168201915b50505050509350828054600181600116156101000203166002900480601f01602080910402602001604051908101604052809291908181526020018280546001816001161561010002031660029004801561110e5780601f106110e35761010080835404028352916020019161110e565b820191906000526020600020905b8154815290600101906020018083116110f157829003601f168201915b50505050509250818054600181600116156101000203166002900480601f0160208091040260200160405190810160405280929190818152602001828054600181600116156101000203166002900480156111aa5780601f1061117f576101008083540402835291602001916111aa565b820191906000526020600020905b81548152906001019060200180831161118d57829003601f168201915b50505050509150808054600181600116156101000203166002900480601f0160208091040260200160405190810160405280929190818152602001828054600181600116156101000203166002900480156112465780601f1061121b57610100808354040283529160200191611246565b820191906000526020600020905b81548152906001019060200180831161122957829003601f168201915b505050505090509450945094509450945091939590929450565b828054600181600116156101000203166002900490600052602060002090601f01602090048101928261129657600085556112dd565b82601f106112af57805160ff19168380011785556112dd565b828001600101855582156112dd579182015b828111156112dc5782518255916020019190600101906112c1565b5b5090506112ea919061137c565b5090565b828054600181600116156101000203166002900490600052602060002090601f016020900481019282611324576000855561136b565b82601f1061133d57805160ff191683800117855561136b565b8280016001018555821561136b579182015b8281111561136a57825182559160200191906001019061134f565b5b509050611378919061137c565b5090565b5b8082111561139557600081600090555060010161137d565b509056fea2646970667358221220091e0f6972f9a4931a3554da987cf055baf5a00d72dbc88278528e07903027cc64736f6c63430007040033";
    # # Instantiate and deploy contract
    Greeter = web3.eth.contract(abi=abi, bytecode=bytecode)
    # # Submit the transaction that deploys the contract
    tx_hash = Greeter.constructor().transact()
    # # Wait for the transaction to be mined, and get the transaction receipt
    tx_receipt = web3.eth.waitForTransactionReceipt(tx_hash)
    print("Certificate is deployed at: ",tx_receipt.contractAddress)
# # Create the contract instance with the newly-deployed address
contract1 = web3.eth.contract(
    address=Web3.toChecksumAddress('0x635BD9A5145489DD58dC724f499C5A972456Ee93'),
    abi=json.loads('[{"anonymous":false,"name":"newPortfolioCreated","inputs":[{"indexed":false,"name":"_pf_no","type":"string","internalType":"string"},{"indexed":false,"name":"_reg_name","type":"string","internalType":"string"},{"indexed":false,"name":"_professor_name","type":"string","internalType":"string"}],"type":"event","payable":false},{"anonymous":false,"name":"pf_CertificateIssued","inputs":[{"indexed":false,"name":"_cert_no","type":"string","internalType":"string"},{"indexed":false,"name":"_pf_no","type":"string","internalType":"string"},{"indexed":false,"name":"_reg_name","type":"string","internalType":"string"},{"indexed":false,"name":"_professor_name","type":"string","internalType":"string"},{"indexed":false,"name":"_score","type":"uint256","internalType":"uint256"}],"type":"event","payable":false},{"constant":true,"name":"PortfolioList","inputs":[{"name":"","type":"uint256","internalType":"uint256"}],"outputs":[{"name":"","type":"string","internalType":"string"}],"type":"function","payable":false,"stateMutability":"view"},{"constant":true,"name":"countPortfolio","inputs":[],"outputs":[{"name":"","type":"uint256","internalType":"uint256"}],"type":"function","payable":false,"stateMutability":"view"},{"constant":true,"name":"getPortfolioStatus","inputs":[{"name":"_pf_no","type":"string","internalType":"string"}],"outputs":[{"name":"","type":"string","internalType":"string"}],"type":"function","payable":false,"stateMutability":"view"},{"constant":true,"name":"getPortfolioInfo","inputs":[{"name":"_pf_no","type":"string","internalType":"string"}],"outputs":[{"name":"","type":"string","internalType":"string"},{"name":"","type":"string","internalType":"string"},{"name":"","type":"string","internalType":"string"},{"name":"","type":"string","internalType":"string"},{"name":"","type":"string","internalType":"string"},{"name":"","type":"bytes","internalType":"bytes"},{"name":"","type":"uint256","internalType":"uint256"}],"type":"function","payable":false,"stateMutability":"view"},{"constant":true,"name":"getPortfolioURL","inputs":[{"name":"_pf_no","type":"string","internalType":"string"}],"outputs":[{"name":"","type":"string","internalType":"string"}],"type":"function","payable":false,"stateMutability":"view"},{"constant":false,"name":"newPortfolio","inputs":[{"name":"_pf_no","type":"string","internalType":"string"},{"name":"_pf_name","type":"string","internalType":"string"},{"name":"_reg_dtime","type":"string","internalType":"string"},{"name":"_reg_name","type":"string","internalType":"string"},{"name":"_professor_name","type":"string","internalType":"string"},{"name":"_professor_pk","type":"bytes","internalType":"bytes"},{"name":"_score","type":"uint256","internalType":"uint256"},{"name":"_pf_status","type":"string","internalType":"string"},{"name":"_pf_url","type":"string","internalType":"string"}],"outputs":[],"type":"function","payable":false,"stateMutability":"nonpayable"}]'),
)

# # Create the contract instance with the newly-deployed address
contract2 = web3.eth.contract(
    address=Web3.toChecksumAddress('0x448871fDf12e65504af8A8da40efc000E12174e0'),
    abi=json.loads('[{"anonymous":false,"name":"pf_CertificateIssued","inputs":[{"indexed":false,"name":"_cert_no","type":"string","internalType":"string"},{"indexed":false,"name":"_pf_no","type":"string","internalType":"string"},{"indexed":false,"name":"_professor_pk","type":"bytes","internalType":"bytes"},{"indexed":false,"name":"_cert_signature","type":"bytes","internalType":"bytes"}],"type":"event","payable":false},{"constant":true,"name":"Portfolio_eCertList","inputs":[{"name":"","type":"uint256","internalType":"uint256"}],"outputs":[{"name":"","type":"string","internalType":"string"}],"type":"function","payable":false,"stateMutability":"view"},{"constant":true,"name":"countPortfolioCerts","inputs":[],"outputs":[{"name":"","type":"uint256","internalType":"uint256"}],"type":"function","payable":false,"stateMutability":"view"},{"constant":true,"name":"getCertificateInfo","inputs":[{"name":"_cert_no","type":"string","internalType":"string"}],"outputs":[{"name":"","type":"string","internalType":"string"},{"name":"","type":"string","internalType":"string"},{"name":"","type":"bytes","internalType":"bytes"},{"name":"","type":"bytes","internalType":"bytes"},{"name":"","type":"bytes","internalType":"bytes"}],"type":"function","payable":false,"stateMutability":"view"},{"constant":false,"name":"issuePortfolioCertificate","inputs":[{"name":"_cert_no","type":"string","internalType":"string"},{"name":"_pf_no","type":"string","internalType":"string"},{"name":"_organizationID","type":"string","internalType":"string"},{"name":"_pf_hash","type":"bytes","internalType":"bytes"},{"name":"_cert_signature","type":"bytes","internalType":"bytes"},{"name":"_professor_pk","type":"bytes","internalType":"bytes"}],"outputs":[],"type":"function","payable":false,"stateMutability":"nonpayable"}]'),
)

@app.route('/setPortfolio', methods=['POST'])
def setPortfolio():
    pf_number="P202104-"+str(countPortfolioEntry()+1)         
    data=Struct1(pf_number,request.form['pf_name'],request.form['reg_dtime'],request.form['reg_name'],request.form['professor_name'],public_key,int(request.form['score']),'Evaluated','www.google.com')
        # # update the greeting
    tx_hash = contract1.functions.newPortfolio(data.pf_no,data.pf_name,data.reg_dtime,data.reg_name,data.professor_name,data.professor_pk,data.score,data.pf_status,data.pf_url).transact()

    # # Wait for transaction to be mined...
    web3.eth.waitForTransactionReceipt(tx_hash)
    
    cert_number="C202104-"+str(countCertificateEntry()+1) 
    organizationID="Korea University"
    cdata=[cert_number,pf_number,request.form['pf_name'],organizationID,request.form['reg_name'],request.form['professor_name'],str(request.form['score']),request.form['reg_dtime']]				
    pfhash=bytes.fromhex(hash_sha256(str(cdata)))    
    signature=bytes.fromhex(sign(private_key,pfhash))
    data2=Struct2(cert_number,pf_number,organizationID,pfhash,signature,public_key)
        # # update the greeting
    tx_hash2 = contract2.functions.issuePortfolioCertificate(data2.cert_no,data2.pf_no,data2.organizationID,data2.pf_hash,data2.cert_signature,data2.professor_pk).transact()

    # # Wait for transaction to be mined...
    web3.eth.waitForTransactionReceipt(tx_hash2)
    QR = qrcode.make([cdata,signature.hex(),public_key.hex()])
    Generate_certificate(cdata,QR)


    # # Display the new greeting value
    data=contract1.functions.getPortfolioInfo(pf_number).call()

    result = {
            'pf_no' : data[0],    
            'pf_name' : data[1],
            'reg_dtime' : data[2],
            'reg_name' : data[3],
            'professor_name' : data[4],
            'professor_pk' : data[5].hex(),
            'score' : data[6],
            'pf_status' : getPortfolioSts(pf_number),
            'pf_url' : getPortfolioLink(pf_number),
    }
    return render_template('registration.html',result=result)

@app.route('/getPortfolio', methods=['POST'])
def printPortfolio():
    # # Display the new greeting value
    try:
        data=contract1.functions.getPortfolioInfo(request.form['pf_no']).call()
        if data[0]:
            result = {
                'pf_no' : data[0],    
                'pf_name' : data[1],
                'reg_dtime' : data[2],
                'reg_name' : data[3],
                'professor_name' : data[4],
                'professor_pk' : data[5].hex(),
                'score' : data[6],
                'pf_status' : getPortfolioSts(request.form['pf_no']),
                'pf_url' : getPortfolioLink(request.form['pf_no']),

            }
        else:
            result=0
    except Exception:
        result = 0    
    return render_template('inquiry.html',result=result)


def countPortfolioEntry():
    # # Display the new greeting value
    return contract1.functions.countPortfolio().call()
def countCertificateEntry():
    # # Display the new greeting value
    return contract2.functions.countPortfolioCerts().call()
def getPortfolioSts(pf_number):
    # # Display the new greeting value
    return contract1.functions.getPortfolioStatus(pf_number).call()

def getPortfolioLink(pf_number):
    # # Display the new greeting value
    return contract1.functions.getPortfolioURL(pf_number).call()



class Struct1(NamedTuple):
    pf_no:str
    pf_name:str
    reg_dtime:str
    reg_name:str
    professor_name:str
    professor_pk:bytes
    score:int
    pf_status:str
    pf_url:str

class Struct2(NamedTuple):
    cert_no:str
    pf_no:str
    organizationID:str
    pf_hash:bytes
    cert_signature:bytes
    professor_pk:bytes



if __name__ == '__main__':
    host = os.environ.get('IP', '0.0.0.0')
    port = int(os.environ.get('PORT', 8000))
    
    app.secret_key = 'super secret key'
    app.config['SESSION_TYPE'] = 'filesystem'

    # sess.init_app(app)
    
    app.run(host= host, port = port, use_reloader = False)