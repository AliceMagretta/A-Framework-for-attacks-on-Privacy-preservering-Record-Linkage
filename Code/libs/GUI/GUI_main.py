import os
from PyQt5 import QtCore, QtWidgets
import sys
import qtawesome
from PyQt5.QtGui import QPalette, QColor, QFont
from PyQt5.QtWidgets import *
import pandas as pd
from PyQt5.QtCore import Qt, pyqtSignal, QRect
from qtpy import QtGui

import Config as C
from libs import importing
from libs import bfEncoding
from libs import evaluating
from libs.attacks import patternmining_attack as pma
from libs.attacks import bit_patternfrequency_attack as bpf
#from libs.attacks import graph_matching_attack as gma
import csv
import gzip
import math
import hashlib
import os.path
import random
import sys
import time
import bitarray
import numpy

# global var
header_field = ['select_all']
global encode_header_combobox
global plain_header_combobox
global data_list
global activat_menu
global datasets

bar_value = 0
pm_dict = {}
activat_menu = None
datasets = {}
result_name_list = ['select a attack result']


# check box
class CheckBoxHeader(QHeaderView):
    # select all signal
    select_all_clicked = pyqtSignal(bool)
    # position and size
    _x_offset = 21
    _y_offset = 10
    _width = 20
    _height = 20
    dataset = 0

    def __init__(self, orientation=Qt.Horizontal, parent=None):
        super(CheckBoxHeader, self).__init__(orientation, parent)
        self.isOn = False  # control select all
        self.dataset = 0

    def setDataset(self, dataset):
        self.dataset = dataset

    # paintSection set the state of QStyleOptionButton
    def paintSection(self, painter, rect, logicalIndex):
        painter.save()
        super(CheckBoxHeader, self).paintSection(painter, rect, logicalIndex)
        painter.restore()
        self._y_offset = int((rect.height() - self._width) / 2.)
        if logicalIndex == 0:
            option = QStyleOptionButton()
            option.rect = QRect(rect.x() + self._x_offset, rect.y() + self._y_offset, self._width, self._height)
            option.state = QStyle.State_Enabled | QStyle.State_Active
            if self.isOn:
                option.state |= QStyle.State_On
            else:
                option.state |= QStyle.State_Off
            self.style().drawControl(QStyle.CE_CheckBox, option, painter)

    # event (press the select_all)
    def mousePressEvent(self, event):
        index = self.logicalIndexAt(event.pos())
        if 0 == index:
            x = self.sectionPosition(index)
            if x + self._x_offset < event.pos().x() < x + self._x_offset + self._width and self._y_offset < event.pos().y() < self._y_offset + self._height:
                if self.isOn:
                    self.isOn = False
                    print(self.isOn)
                else:
                    self.isOn = True
                    print(self.isOn)
                    # select_all_clicked
                self.select_all_clicked.emit(self.isOn)
                self.updateSection(0)
        super(CheckBoxHeader, self).mousePressEvent(event)

    #
    def change_state(self, isOn):
        # total control
        if self.dataset == 0:
            if isOn:
                # select all encode to checked
                for i in encode_header_combobox:
                    i.setCheckState(Qt.Checked)
            else:
                for i in encode_header_combobox:
                    i.setCheckState(Qt.Unchecked)
        else:
            if isOn:
                # select all plain to checked
                for i in plain_header_combobox:
                    i.setCheckState(Qt.Checked)
            else:
                for i in plain_header_combobox:
                    i.setCheckState(Qt.Unchecked)


class Color(QWidget):

    def __init__(self, color):
        super(Color, self).__init__()
        self.setAutoFillBackground(True)

        palette = self.palette()
        palette.setColor(QPalette.Window, QColor(color))
        self.setPalette(palette)


# Main Menu
class MainUi(QtWidgets.QMainWindow):
    def __init__(self):
        super().__init__()
        self.init_ui()

    # initial UI
    def init_ui(self):
        self.setFixedSize(2200, 1200)
        self.main_widget = QtWidgets.QWidget()  # 创建窗口主部件
        self.main_layout = QtWidgets.QGridLayout()  # 创建主部件的网格布局
        self.main_widget.setLayout(self.main_layout)  # 设置窗口主部件布局为网格布局

        self.left_widget = QtWidgets.QWidget()  # 创建左侧部件
        self.left_widget.setObjectName('left_widget')  # 部件命名，设置样式用
        self.left_layout = QtWidgets.QGridLayout()  # 创建左侧部件的网格布局层
        self.left_widget.setLayout(self.left_layout)  # 设置左侧部件布局为网格
        self.main_layout.addWidget(self.left_widget, 0, 0, 12, 2)  # 左侧部件在第0行第0列，占12行2列
        self.setCentralWidget(self.main_widget)  # 设置窗口主部件

        self.left_label_1 = QtWidgets.QPushButton('welcome')
        self.left_label_1.setObjectName('left_label')
        self.left_label_3 = QtWidgets.QPushButton("tools")
        self.left_label_3.setObjectName('left_label')

        self.left_button_1 = QtWidgets.QPushButton(qtawesome.icon('fa.database', color='white'), "Dataset")
        self.left_button_1.setObjectName('left_button')
        self.left_button_1.clicked.connect(lambda: self.setRightWidget(C.FLAG_DATASET))
        self.left_button_2 = QtWidgets.QPushButton(qtawesome.icon('fa.key', color='white'), "Encoding")
        self.left_button_2.setObjectName('left_button')
        self.left_button_2.clicked.connect(lambda: self.setRightWidget(C.FLAG_ENCODING))
        self.left_button_3 = QtWidgets.QPushButton(qtawesome.icon('fa.rocket', color='white'), "Attack")
        self.left_button_3.setObjectName('left_button')
        self.left_button_3.clicked.connect(lambda: self.setRightWidget(C.FLAG_ATTACK))
        self.left_button_4 = QtWidgets.QPushButton(qtawesome.icon('fa.edit', color='white'), "Evaluation")
        self.left_button_4.setObjectName('left_button')
        self.left_button_4.clicked.connect(lambda: self.setRightWidget(C.FLAG_EVAL))
        self.left_button_5 = QtWidgets.QPushButton()
        self.left_button_6 = QtWidgets.QPushButton()
        self.left_button_7 = QtWidgets.QPushButton()
        self.left_button_8 = QtWidgets.QPushButton(qtawesome.icon('fa.shield', color='white'), "Comparison")
        self.left_button_8.setObjectName('left_button')
        self.left_button_8.clicked.connect(lambda: self.setRightWidget(C.FLAG_COMP))
        self.left_button_9 = QtWidgets.QPushButton(qtawesome.icon('fa.info', color='white'), "Guide")
        self.left_button_9.setObjectName('left_button')
        self.left_button_9.clicked.connect(lambda: self.setRightWidget(C.FLAG_GUIDE))
        self.left_xxx = QtWidgets.QPushButton(" ")

        self.left_layout.addWidget(self.left_label_1, 1, 0, 1, 3)
        self.left_layout.addWidget(self.left_button_1, 2, 0, 1, 3)
        self.left_layout.addWidget(self.left_button_2, 3, 0, 1, 3)
        self.left_layout.addWidget(self.left_button_3, 4, 0, 1, 3)
        self.left_layout.addWidget(self.left_button_4, 6, 0, 1, 3)
        self.left_layout.addWidget(self.left_label_3, 8, 0, 1, 3)
        self.left_layout.addWidget(self.left_button_8, 9, 0, 1, 3)
        self.left_layout.addWidget(self.left_button_9, 10, 0, 1, 3)
        self.left_layout.addWidget(self.left_button_5, 11, 0, 1, 3)
        self.left_layout.addWidget(self.left_button_6, 12, 0, 1, 3)
        self.left_layout.addWidget(self.left_button_7, 7, 0, 1, 3)

        # set the style of left widget
        self.left_widget.setStyleSheet('''
            QPushButton{border:none;color:white;}
            QPushButton#left_label{
                border:none;
                border-bottom:1px solid white;
                padding-bottom:3px;
                font-size:28px;
                font-weight:1800;
                font-family: "Helvetica Neue", Helvetica, Arial, sans-serif;
            }
            QPushButton#left_button{
                width:30px;
                font-size:25px;
            }
            QPushButton#left_button:hover{font-weight:700;}
            QWidget#left_widget{
                background:#607d8b;
                border-top:1px solid white;
                border-bottom:1px solid white;
                border-left:1px solid white;
            }
        ''')
        self.right_widget = None
        self.right_widget_p = None
        self.setRightWidget()
        self.main_layout.setSpacing(0)

    # set content of right widget
    def setRightWidget(self, flag=C.FLAG_GUIDE):
        # dataset
        if flag == C.FLAG_DATASET:
            self.right_widget = self.dataset_management()
        # encoding
        elif flag == C.FLAG_ENCODING:
            self.right_widget = self.encoding_management()
        # attack
        elif flag == C.FLAG_ATTACK:
            self.right_widget = self.attack_management()
        # evaluation
        elif flag == C.FLAG_EVAL:
            self.right_widget = self.evaluation_management()
        # comparison
        elif flag == C.FLAG_COMP:
            self.right_widget = self.comparison()
        # guide
        elif flag == C.FLAG_GUIDE:
            self.right_widget = self.guide()

    # datasets manager
    def dataset_management(self):
        global dataset_names_list
        if self.right_widget:
            self.main_layout.removeWidget(self.right_widget)  # remove exist right widget
        self.setWindowTitle('attack simulator - dataset manage')
        self.setLeftMenu(self.left_button_1)  # select button effect
        self.right_widget = QtWidgets.QWidget()  # create new right widget
        self.right_widget.setObjectName('right_widget')
        self.verticalLayout = QtWidgets.QVBoxLayout()
        self.verticalLayout.setObjectName("verticalLayout")

        self.right_layout = self.verticalLayout
        self.right_widget.setLayout(self.right_layout)  # set right widget to layout

        # right_widget is beginning at row 0, column 2, take 12 rows, 10 columns
        self.main_layout.addWidget(self.right_widget, 0, 2, 12, 10)

        self.widget = QtWidgets.QWidget()
        self.horizontalLayout = QtWidgets.QHBoxLayout(self.widget)
        self.horizontalLayout.setObjectName("horizontalLayout")
        self.label = QtWidgets.QLabel(self.widget)
        font = QtGui.QFont()
        font.setPointSize(12)
        self.label.setFont(font)
        self.label.setObjectName("label")
        self.horizontalLayout.addWidget(self.label)

        # encode dataset comboBox1
        self.cb1 = QComboBox(self)
        # fill the comboBox
        self.cb1.addItem('select a dataset')
        dataset_names_list = self.getDatasetNameList()
        print(dataset_names_list)
        for dataset in dataset_names_list:
            self.cb1.addItem(str(dataset))
        self.cb1.currentIndexChanged[int].connect(lambda: self.getDataList(self.cb1.currentText(), C.FLAG_DATASET, 0))
        self.cb1.setStyleSheet(''' text-align : center;
                                              height : 50px;
                                              padding-left: 10px;
                                              font : 24px  ''')
        self.horizontalLayout.addWidget(self.cb1)
        # delete dataset
        self.pushButton_del = QtWidgets.QPushButton(self.widget)
        self.pushButton_del.setObjectName("pushButton_del")
        self.horizontalLayout.addWidget(self.pushButton_del)
        self.pushButton_del.clicked.connect(lambda: self.dataDelete(self.cb1.currentText()))
        self.pushButton_del.setStyleSheet(''' text-align : center;
                                              background-color : #f44336;
                                              height : 60px;
                                              width: 160px;
                                              border-style: outset;
                                              border-radius: 50px;
                                              color: #fff;
                                              font : 22px  ''')

        # space
        spacerItem = QtWidgets.QSpacerItem(40, 20, QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Minimum)
        self.horizontalLayout.addItem(spacerItem)

        # import dataset
        self.pushButton_3 = QtWidgets.QPushButton(self.widget)
        self.pushButton_3.setObjectName("pushButton")
        self.horizontalLayout.addWidget(self.pushButton_3)
        self.pushButton_3.clicked.connect(lambda: self.open_file())
        self.pushButton_3.setStyleSheet(''' text-align : center;
                                              background-color : #009688;
                                              height : 80px;
                                              width: 170px;
                                              border-style: outset;
                                              border-radius: 100px;
                                              color: #fff;
                                              font : 26px  ''')

        # table form
        self.verticalLayout.addWidget(self.widget)
        self.tableWidget = QtWidgets.QTableWidget()
        self.tableWidget.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectRows)
        self.tableWidget.setObjectName("tableWidget")
        self.verticalLayout.addWidget(self.tableWidget)

        # set shown values
        _translate = QtCore.QCoreApplication.translate
        self.label.setText(_translate("Form", "select dataset:"))
        self.pushButton_del.setText(_translate("Form", "delete seleted"))
        self.pushButton_3.setText(_translate("Form", "import new"))

        return self.right_widget

    # encoding manager
    def encoding_management(self):
        global dataset_names_list
        global encode_header_combobox
        global plain_header_combobox
        encode_header_combobox = []
        plain_header_combobox = []
        if self.right_widget:
            self.main_layout.removeWidget(self.right_widget)  # remove exist right widget
        if self.right_widget_p:
            self.main_layout.removeWidget(self.right_widget_p)  # remove exist right widget
        self.setWindowTitle('attack simulator - dataset manage')
        self.setLeftMenu(self.left_button_2)  # select button effect

        # encoding methods choose
        encode_methods_ls = ["MDK", "Bloom Filter"]
        value, ok = QInputDialog.getItem(self, "Encoding Method",
                                         "Before encode dataset\n\nplease select a encoding method:", encode_methods_ls,
                                         1, True)
        if not ok:
            QMessageBox.information(self, 'ERROR',
                                    "selected method is invalid! Please try again!")
            value, ok = QInputDialog.getItem(self, "Encoding Method",
                                             "Before encode dataset\n\nplease select a encoding method:",
                                             encode_methods_ls, 1, True)
        if value == 'MDK':
            QMessageBox.information(self, 'ERROR',
                                    "Not support chosen methods now!")

        # right widget for encoded dataset
        self.right_widget = QtWidgets.QWidget()  # create new right widget
        self.right_widget.setObjectName('right_widget')
        self.verticalLayout = QtWidgets.QVBoxLayout()
        self.verticalLayout.setObjectName("verticalLayout")
        self.right_layout = self.verticalLayout
        self.right_widget.setLayout(self.right_layout)  # set right widget to layout
        self.main_layout.addWidget(self.right_widget, 0, 2, 6, 10)  # begin at row 6, column 2, take 12 rows, 10 columns

        self.widget = QtWidgets.QWidget()
        self.horizontalLayout = QtWidgets.QHBoxLayout(self.widget)
        self.horizontalLayout.setObjectName("horizontalLayout")
        self.label = QtWidgets.QLabel(self.widget)
        font = QtGui.QFont()
        font.setPointSize(8)
        self.label.setFont(font)
        self.label.setObjectName("label")
        self.horizontalLayout.addWidget(self.label)

        # right widget for plain_text dataset
        self.right_widget_p = QtWidgets.QWidget()  # create new right widget
        self.right_widget_p.setObjectName('right_widget')
        self.verticalLayout_p = QtWidgets.QVBoxLayout()
        self.verticalLayout_p.setObjectName("verticalLayout")
        self.right_layout_p = self.verticalLayout_p
        self.right_widget_p.setLayout(self.right_layout_p)  # set right widget to layout
        self.main_layout.addWidget(self.right_widget_p, 6, 2, 6,
                                   10)  # begin at row 6, column 2, take 12 rows, 10 columns

        self.widget_p = QtWidgets.QWidget()
        self.horizontalLayout_p = QtWidgets.QHBoxLayout(self.widget_p)
        self.horizontalLayout_p.setObjectName("horizontalLayout")
        self.label_p = QtWidgets.QLabel(self.widget_p)
        font = QtGui.QFont()
        font.setPointSize(8)
        self.label_p.setFont(font)
        self.label_p.setObjectName("label")
        self.horizontalLayout_p.addWidget(self.label_p)

        # ---------------------------------------------------------------------
        # encode parameters
        # encode dataset comboBox1
        self.cb1 = QComboBox(self)
        self.cb1.addItem('select encode dataset')
        dataset_names_list = self.getDatasetNameList()
        print(dataset_names_list)
        for dataset in dataset_names_list:  # fill the comboBox
            self.cb1.addItem(str(dataset))
        self.cb1.currentIndexChanged[int].connect(lambda: self.getDataList(self.cb1.currentText(), C.FLAG_ENCODING, 0))
        self.cb1.setStyleSheet(''' text-align : center;
                                                     height : 50px;
                                                     padding-left: 10px;
                                                     font : 18px  ''')
        self.horizontalLayout.addWidget(self.cb1)

        # encode column sep char
        self.input_s = QtWidgets.QLineEdit(self.widget)
        self.input_s.setObjectName("input_p")
        self.horizontalLayout.addWidget(self.input_s)
        self.input_s.setText('","')
        self.input_s.setStyleSheet(''' height : 30px;
                                                           border-style: outset;
                                                           padding-left: 5px;
                                                           border: 1px solid #ccc;
                                                           border-radius: 5px;
                                                           font : 12px  ''')
        self.input_s.setToolTip("character to be used to separate fields in the encode input file")
        self.input_s.setToolTipDuration(3000)

        # space
        spacerItem = QtWidgets.QSpacerItem(1, 2, QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Minimum)
        self.horizontalLayout.addItem(spacerItem)

        # q
        self.label_2 = QtWidgets.QLabel(self.widget)
        self.label_2.setObjectName("label_2")
        self.label_2.setToolTip("q is the length of q-grams to use")
        self.label_2.setToolTipDuration(4000)
        self.horizontalLayout.addWidget(self.label_2)
        self.input_q = QtWidgets.QLineEdit(self.widget)
        self.input_q.setObjectName("input_q")
        self.horizontalLayout.addWidget(self.input_q)
        self.input_q.setStyleSheet(''' height : 30px;
                                                     border-style: outset;
                                                     padding-left: 5px;
                                                     border: 1px solid #ccc;
                                                     border-radius: 5px;
                                                     font : 12px  ''')

        # num_hash_funct
        self.label_3 = QtWidgets.QLabel(self.widget)
        self.label_3.setObjectName("label_3")
        self.label_3.setToolTip("number of hash function is a positive number or 'opt' (to fill BF 50%)")
        self.label_3.setToolTipDuration(4000)
        self.horizontalLayout.addWidget(self.label_3)
        self.input_nhf = QtWidgets.QLineEdit(self.widget)
        self.input_nhf.setObjectName("input_nhf")
        self.horizontalLayout.addWidget(self.input_nhf)
        self.input_nhf.setStyleSheet(''' height : 30px;
                                                     border-style: outset;
                                                     padding-left: 5px;
                                                     border: 1px solid #ccc;
                                                     border-radius: 5px;
                                                     font : 16px  ''')

        # bf_len
        self.label_4 = QtWidgets.QLabel(self.widget)
        self.label_4.setObjectName("label_4")
        self.label_4.setToolTip("bf_len is the length of Bloom filters")
        self.label_4.setToolTipDuration(4000)
        self.horizontalLayout.addWidget(self.label_4)
        self.input_bfl = QtWidgets.QLineEdit(self.widget)
        self.input_bfl.setObjectName("input_bfl")
        self.horizontalLayout.addWidget(self.input_bfl)
        self.input_bfl.setStyleSheet(''' height : 30px;
                                                     border-style: outset;
                                                     padding-left: 5px;
                                                     border: 1px solid #ccc;
                                                     border-radius: 5px;
                                                     font : 16px  ''')

        # space
        spacerItem = QtWidgets.QSpacerItem(1, 1, QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Minimum)
        self.horizontalLayout.addItem(spacerItem)

        # hash type
        self.cb2 = QComboBox(self)
        self.cb2.addItem('select hash type')
        self.cb2.addItem('dh')
        self.cb2.addItem('rh')
        self.cb2.addItem('edh')
        self.cb2.addItem('th')
        self.cb2.setStyleSheet(''' text-align : center;
                                                      height : 50px;
                                                      padding-left: 5px;
                                                      font : 18px  ''')
        self.cb2.setToolTip("hash_type is either DH (double-hashing) or RH (random hashing)")
        self.cb2.setToolTipDuration(4000)
        self.horizontalLayout.addWidget(self.cb2)

        # bf_harden
        self.cb3 = QComboBox(self)
        self.cb3.addItem('select harden type')
        self.cb3.addItem('none')
        self.cb3.addItem('balance')
        self.cb3.addItem('fold')
        self.cb3.addItem('rule90')
        self.cb3.addItem('mchain')
        self.cb3.addItem('salt')
        self.cb3.setStyleSheet(''' text-align : center;
                                                      height : 50px;
                                                      padding-left: 5px;
                                                      font : 18px  ''')
        self.cb3.setToolTip("bf_harden is either None, 'balance' or 'fold'\nfor different BF hardening techniques")
        self.cb3.setToolTipDuration(4000)
        self.horizontalLayout.addWidget(self.cb3)

        # table form
        self.verticalLayout.addWidget(self.widget)
        self.tableWidget = QtWidgets.QTableWidget()
        self.tableWidget.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectRows)
        self.tableWidget.setObjectName("tableWidget")
        self.verticalLayout.addWidget(self.tableWidget)

        # set shown values
        _translate = QtCore.QCoreApplication.translate
        self.label.setText(_translate("Form", "select dataset:"))
        self.input_s.setText(_translate("Form", '","'))
        self.label_2.setText(_translate("Form", "q:"))
        self.label_3.setText(_translate("Form", "num_hash_funct:"))
        self.label_4.setText(_translate("Form", "bf_len:"))

        # select box
        header = CheckBoxHeader()
        header.setDataset(dataset=0)
        self.tableWidget.setHorizontalHeader(header)
        header.select_all_clicked.connect(header.change_state)

        # ---------------------------------------------------------------------
        # plain_text parameters
        # encode dataset comboBox1
        self.cb1_p = QComboBox(self)
        self.cb1_p.addItem('select plain_text dataset')
        dataset_names_list = self.getDatasetNameList()
        print(dataset_names_list)
        for dataset in dataset_names_list:  # fill the comboBox
            self.cb1_p.addItem(str(dataset))
        self.cb1_p.currentIndexChanged[int].connect(
            lambda: self.getDataList(self.cb1_p.currentText(), C.FLAG_ENCODING, 1))
        self.cb1_p.setStyleSheet(''' text-align : center;
                                                             height : 50px;
                                                             padding-left: 10px;
                                                             font : 18px  ''')
        self.horizontalLayout_p.addWidget(self.cb1_p)

        # plaintext column sep char
        self.input_s_p = QtWidgets.QLineEdit(self.widget)
        self.input_s_p.setObjectName("input_p")
        self.input_s_p.setText('","')
        self.horizontalLayout_p.addWidget(self.input_s_p)
        self.input_s_p.setStyleSheet(''' height : 30px;
                                                           border-style: outset;
                                                           padding-left: 5px;
                                                           border: 1px solid #ccc;
                                                           border-radius: 5px;
                                                           font : 16px  ''')
        self.input_s_p.setToolTip("character to be used to separate fields in the encode input file")
        self.input_s_p.setToolTipDuration(3000)

        # space
        spacerItem = QtWidgets.QSpacerItem(1, 1, QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Minimum)
        self.horizontalLayout_p.addItem(spacerItem)

        # bf_encode
        self.cb4_p = QComboBox(self)
        self.cb4_p.addItem('select encode type')
        self.cb4_p.addItem('abf')
        self.cb4_p.addItem('clk')
        self.cb4_p.addItem('rbf-s')
        self.cb4_p.addItem('clkrbf')
        self.cb4_p.setStyleSheet(''' text-align : center;
                                                              height : 50px;
                                                              padding-left: 5px;
                                                              font : 18px  ''')
        self.cb4_p.setToolTip("bf_encode is the Bloom filter encoding method")
        self.cb4_p.setToolTipDuration(3000)
        self.horizontalLayout_p.addWidget(self.cb4_p)


        # encode parameter list
        self.input_p_p = QtWidgets.QLineEdit(self.widget)
        self.input_p_p.setObjectName("input_p")
        self.horizontalLayout_p.addWidget(self.input_p_p)
        self.input_p_p.setStyleSheet(''' height : 50px;
                                                                  border-style: outset;
                                                                  padding-left: 5px;
                                                                  border: 1px solid #ccc;
                                                                  border-radius: 5px;
                                                                  font : 15px  ''')
        self.input_p_p.setToolTip("This is a list of parameters that need to be defined\n based on encoding method ("
                                  "otherwise None)\n if encoding method == RBF\n  parameter list = num_bits_list\n - "
                                  "num_bits_list  is the list of percentages of number of bits need \nto be selected "
                                  "from each ABF to generate RBF\nif encoding method == CLKRBF \nparameter list = "
                                  "num_hash_funct_list \n - num_hash_funct_list is a list of hash functions for each "
                                  "encoding attribute")
        self.input_p_p.setToolTipDuration(10000)

        # harden parameter list
        self.input_h_p = QtWidgets.QLineEdit(self.widget)
        self.input_h_p.setObjectName("input_p")
        self.horizontalLayout_p.addWidget(self.input_h_p)
        self.input_h_p.setStyleSheet(''' height : 50px;
                                                                          border-style: outset;
                                                                          padding-left: 5px;
                                                                          border: 1px solid #ccc;
                                                                          border-radius: 5px;
                                                                          font : 15px  ''')
        self.input_h_p.setToolTip("is a list of parameters that need to be defined based on hardening method\nif "
                                  "hardening method == mchain\n parameter list = [chain_len, sel_method]\n- chain_len "
                                  "  is the number of extra q-grams to be added\n- sel_method  the method of how "
                                  "q-grams are being selected. \nCan either be probabilistic or frequency based if "
                                  "hardening method == balance\n parameter list = [random_seed]\n- random_seed   set "
                                  "to True if random seed need to be defined")
        self.input_h_p.setToolTipDuration(10000)

        # encode button
        self.pushButton_encode = QtWidgets.QPushButton(self.widget)
        self.pushButton_encode.setObjectName("pushButton_encode")
        self.horizontalLayout_p.addWidget(self.pushButton_encode)
        self.pushButton_encode.clicked.connect(
            lambda: self.encode(self.cb1.currentText(), self.cb1_p.currentText(), self.input_q.text(),
                                self.cb2.currentText(), self.input_nhf.text(), self.input_bfl.text(),
                                self.cb3.currentText(),
                                self.getAttriList(0), self.getAttriList(1), self.cb4_p.currentText(),
                                self.input_s.text(), self.input_s_p.text(), self.input_p_p.text(),
                                self.input_h_p.text()))
        self.pushButton_encode.setStyleSheet(''' text-align : center;
                                                     background-color : #f44336;
                                                     height : 60px;
                                                     width: 160px;
                                                     border-style: outset;
                                                     border-radius: 50px;
                                                     color: #fff;
                                                     font : 22px  ''')

        # table form
        self.verticalLayout_p.addWidget(self.widget_p)
        self.tableWidget_p = QtWidgets.QTableWidget()
        self.tableWidget_p.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectRows)
        self.tableWidget_p.setObjectName("tableWidget")
        self.verticalLayout_p.addWidget(self.tableWidget_p)

        # set shown values
        _translate = QtCore.QCoreApplication.translate
        self.label_p.setText(_translate("Form", "select dataset:"))
        self.input_s_p.setText(_translate("Form", '","'))
        self.input_p_p.setText(_translate("Form", "encode parameter list"))
        self.input_h_p.setText(_translate("Form", "harden parameter list"))
        self.pushButton_encode.setText(_translate("Form", "Encode"))

        # select box
        header1 = CheckBoxHeader()
        header1.setDataset(dataset=1)
        self.tableWidget_p.setHorizontalHeader(header1)
        header1.select_all_clicked.connect(header1.change_state)

        return self.right_widget

    # attack manager
    def attack_management(self):

        if self.right_widget:
            self.main_layout.removeWidget(self.right_widget)  # remove exist right widget
        if self.right_widget_p:
            self.main_layout.removeWidget(self.right_widget_p)  # remove exist right widget

        self.setWindowTitle('attack simulator - attack manage')
        self.setLeftMenu(self.left_button_3)  # select button effect

        # encoding methods choose
        attack_methods_ls = ["bit pattern frequency based", "pattern mining based"]
        value, ok = QInputDialog.getItem(self, "Attacking Method",
                                         "Before conduct Attack\n\nplease select a attack method:", attack_methods_ls,
                                         1, True)
        if not ok:
            QMessageBox.information(self, 'ERROR',
                                    "selected method is invalid! Please try again!")
            value, ok = QInputDialog.getItem(self, "Attacking Method",
                                             "Before conduct Attack\n\nplease select a attack method:",
                                             attack_methods_ls,
                                             1, True)

        #
        # right widget for param 1
        self.right_widget = QtWidgets.QWidget()  # create new right widget
        self.right_widget.setObjectName('right_widget')
        self.verticalLayout = QtWidgets.QVBoxLayout()
        self.verticalLayout.setObjectName("verticalLayout")
        self.right_layout = self.verticalLayout
        self.right_widget.setLayout(self.right_layout)  # set right widget to layout
        self.main_layout.addWidget(self.right_widget, 0, 2, 1, 8)  # begin at row 6, column 2, take 12 rows, 10 columns

        self.widget = QtWidgets.QWidget()
        self.horizontalLayout = QtWidgets.QHBoxLayout(self.widget)
        self.horizontalLayout.setObjectName("horizontalLayout")

        # right widget for param 2,3,4
        self.right_widget_p = QtWidgets.QWidget()  # create new right widget
        self.right_widget_p.setObjectName('right_widget')
        self.verticalLayout_p = QtWidgets.QVBoxLayout()
        self.verticalLayout_p.setObjectName("verticalLayout")
        self.right_layout_p = self.verticalLayout_p
        self.right_widget_p.setLayout(self.right_layout_p)  # set right widget to layout
        self.main_layout.addWidget(self.right_widget_p, 1, 2, 9,
                                   8)  # begin at row 6, column 2, take 12 rows, 10 columns

        self.widget_p = QtWidgets.QWidget()
        self.horizontalLayout_p = QtWidgets.QHBoxLayout(self.widget_p)
        self.horizontalLayout_p.setObjectName("horizontalLayout")

        # right widget button
        self.right_widget_b = QtWidgets.QWidget()  # create new right widget
        self.right_widget_b.setObjectName('right_widget')
        self.verticalLayout_b = QtWidgets.QVBoxLayout()
        self.verticalLayout_b.setObjectName("verticalLayout")
        self.right_layout_b = self.verticalLayout_b
        self.right_widget_b.setLayout(self.right_layout_b)  # set right widget to layout
        self.main_layout.addWidget(self.right_widget_b, 10, 2, 2,
                                   8)  # begin at row 6, column 2, take 12 rows, 10 columns

        self.widget_b = QtWidgets.QWidget()
        self.horizontalLayout_b = QtWidgets.QHBoxLayout(self.widget_b)
        self.horizontalLayout_b.setObjectName("horizontalLayout")
        # ---------------------------------------------------------------------
        if value == 'pattern mining based':
            # pattern mining attack parameters
            # param_1 : pattern_mine_method_str
            self.label = QtWidgets.QLabel(self.widget)
            font = QtGui.QFont()
            font.setPointSize(8)
            self.label.setFont(font)
            self.label.setObjectName("label")
            self.label.setToolTip("The name of the algorithm use for pattern mining. Select one or more")
            self.label.setToolTipDuration(3000)
            self.horizontalLayout.addWidget(self.label)

            self.ckb1 = QCheckBox(self)
            self.ckb1.setText('apriori')
            self.horizontalLayout.addWidget(self.ckb1)
            self.ckb2 = QCheckBox(self)
            self.ckb2.setText('mapriori')
            self.horizontalLayout.addWidget(self.ckb2)
            self.ckb3 = QCheckBox(self)
            self.ckb3.setText('maxminer')
            self.ckb3.setChecked(True)
            self.horizontalLayout.addWidget(self.ckb3)
            self.ckb4 = QCheckBox(self)
            self.ckb4.setText('hmine')
            self.horizontalLayout.addWidget(self.ckb4)

            self.ckb1.setToolTip("Classical breath-first Apriori")
            self.ckb1.setToolTipDuration(3000)
            self.ckb1.setStyleSheet(''' text-align : center;
                                                         height : 50px;
                                                         padding-left: 10px;
                                                         font : 18px  ''')
            self.ckb2.setToolTip("Memory-based Apriori")
            self.ckb2.setToolTipDuration(3000)
            self.ckb2.setStyleSheet(''' text-align : center;
                                                                     height : 50px;
                                                                     padding-left: 10px;
                                                                     font : 18px  ''')
            self.ckb3.setToolTip("The breath-first Max-Minor approach")
            self.ckb3.setToolTipDuration(3000)
            self.ckb3.setStyleSheet(''' text-align : center;
                                                                     height : 50px;
                                                                     padding-left: 10px;
                                                                     font : 18px  ''')

            # space
            spacerItem = QtWidgets.QSpacerItem(2, 20, QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Minimum)
            self.horizontalLayout.addItem(spacerItem)

            # stop_iter_perc
            self.label_2 = QtWidgets.QLabel(self.widget)
            self.label_2.setObjectName("label_2")
            self.label_2.setToolTip("The minimum percentage difference required between\n"
                                    "the two most frequent q-grams to continue the\n"
                                    "recursive Apriori pattern mining approach.\n"
                                    "value : > 0.0 and < 100.0")
            self.label_2.setToolTipDuration(4000)
            self.horizontalLayout.addWidget(self.label_2)

            self.input_1 = QtWidgets.QLineEdit(self.widget)
            self.input_1.setObjectName("input_1")
            self.input_1.setText("1.0")
            self.horizontalLayout.addWidget(self.input_1)

            # space
            spacerItem = QtWidgets.QSpacerItem(1, 20, QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Minimum)
            self.horizontalLayout.addItem(spacerItem)

            # stop_iter_perc_lm
            self.label_3 = QtWidgets.QLabel(self.widget)
            self.label_3.setObjectName("label_3")
            self.label_3.setToolTip("The minimum percentage difference required between\n"
                                    "the two q-grams with highest condional probabilities\n"
                                    "in language model.\n"
                                    "value : > 0.0 and < 100.0")
            self.label_3.setToolTipDuration(4000)
            self.horizontalLayout.addWidget(self.label_3)
            self.input_2 = QtWidgets.QLineEdit(self.widget)
            self.input_2.setObjectName("input_2")
            self.input_2.setText("5.0")
            self.horizontalLayout.addWidget(self.input_2)
            self.input_2.setStyleSheet(''' height : 30px;
                                                         border-style: outset;
                                                         padding-left: 5px;
                                                         border: 1px solid #ccc;
                                                         border-radius: 5px;
                                                         font : 12px  ''')

            # space
            spacerItem = QtWidgets.QSpacerItem(1, 20, QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Minimum)
            self.horizontalLayout.addItem(spacerItem)

            # min_part_size
            self.label_4 = QtWidgets.QLabel(self.widget)
            self.label_4.setObjectName("label_4")
            self.label_4.setToolTip("The minimum number of BFs in a 'partition' for the\n"
                                    "partition to be used with the Apriori algorithm.\n"
                                    "value : > 1")
            self.label_4.setToolTipDuration(4000)
            self.horizontalLayout.addWidget(self.label_4)
            self.input_3 = QtWidgets.QLineEdit(self.widget)
            self.input_3.setObjectName("input_3")
            self.input_3.setText("10000")
            self.horizontalLayout.addWidget(self.input_3)
            self.input_3.setStyleSheet(''' height : 30px;
                                                         border-style: outset;
                                                         padding-left: 5px;
                                                         border: 1px solid #ccc;
                                                         border-radius: 5px;
                                                         font : 16px  ''')

            # max_num_many
            self.label_5 = QtWidgets.QLabel(self.widget)
            self.label_5.setObjectName("label_5")
            self.label_5.setToolTip("For the re-identification step, the maximum number\n"
                                    "of 1-to-many matches to consider\n"
                                    "value : > 1")
            self.label_5.setToolTipDuration(3000)
            self.horizontalLayout_p.addWidget(self.label_5)
            self.input_4 = QtWidgets.QLineEdit(self.widget)
            self.input_4.setObjectName("input_4")
            self.input_4.setText("10")
            self.horizontalLayout_p.addWidget(self.input_4)
            self.input_4.setStyleSheet(''' height : 30px;
                                                         border-style: outset;
                                                         padding-left: 5px;
                                                         border: 1px solid #ccc;
                                                         border-radius: 5px;
                                                         font : 16px  ''')

            # space
            spacerItem = QtWidgets.QSpacerItem(1, 20, QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Minimum)
            self.horizontalLayout.addItem(spacerItem)

            # re_id_method
            self.cb2 = QComboBox(self)
            self.cb2.addItem('select re-id method:')
            self.cb2.addItem('all')
            self.cb2.addItem('set_inter')
            self.cb2.addItem('bf_tuple')
            self.cb2.addItem('none')
            self.cb2.setStyleSheet(''' text-align : center;
                                                          height : 50px;
                                                          padding-left: 5px;
                                                          font : 18px  ''')
            self.cb2.setToolTip("The approach to be used for re-identification,\n"
                                "if set to 'none' then no re-identification will be attempted")
            self.cb2.setToolTipDuration(3000)
            self.cb2.setCurrentIndex(3)
            self.horizontalLayout_p.addWidget(self.cb2)

            # space
            spacerItem = QtWidgets.QSpacerItem(1, 20, QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Minimum)
            self.horizontalLayout.addItem(spacerItem)

            # expand_lang_model
            self.cb3 = QComboBox(self)
            self.cb3.addItem('select expand_lang_model')
            self.cb3.addItem('single')
            self.cb3.addItem('tuple')
            self.cb3.addItem('all')
            self.cb3.setStyleSheet(''' text-align : center;
                                                          height : 50px;
                                                          padding-left: 5px;
                                                          font : 18px  ''')
            self.cb3.setToolTip("select one language model type")
            self.cb3.setToolTipDuration(2000)
            self.cb3.setCurrentIndex(1)
            self.horizontalLayout_p.addWidget(self.cb3)

            # space
            spacerItem = QtWidgets.QSpacerItem(1, 20, QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Minimum)
            self.horizontalLayout.addItem(spacerItem)

            # lang_model_min_freq
            self.label_6 = QtWidgets.QLabel(self.widget)
            self.label_6.setObjectName("label_6")
            self.label_6.setToolTip("For the language model, the minimum frequency\n"
                                    "value : > 1")
            self.label_6.setToolTipDuration(3000)
            self.horizontalLayout_p.addWidget(self.label_6)
            self.input_5 = QtWidgets.QLineEdit(self.widget)
            self.input_5.setObjectName("input_5")
            self.input_5.setText("5")
            self.horizontalLayout_p.addWidget(self.input_5)
            self.input_5.setStyleSheet(''' height : 30px;
                                                                    border-style: outset;
                                                                    padding-left: 5px;
                                                                    border: 1px solid #ccc;
                                                                    border-radius: 5px;
                                                                    font : 16px  ''')

            # space
            spacerItem = QtWidgets.QSpacerItem(1, 20, QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Minimum)
            self.horizontalLayout.addItem(spacerItem)

            # space
            spacerItem = QtWidgets.QSpacerItem(2, 20, QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Minimum)
            self.horizontalLayout_b.addItem(spacerItem)

            # Progress bar
            self.pgb = QtWidgets.QProgressBar(self.widget)
            self.pgb.move(50, 50)
            self.pgb.resize(250, 20)
            self.pgb.setStyleSheet(
                "QProgressBar { border: 2px solid grey; border-radius: 5px; color: rgb(20,20,20);  background-color: "
                "#FFFFFF; text-align: center;}QProgressBar::chunk {background-color: rgb(100,200,200); border-radius: "
                "10px; margin: 0.1px;  width: 1px;}")

            font = QFont()
            font.setBold(True)
            font.setWeight(30)
            self.pgb.setFont(font)
            self.pv = 0
            self.pgb.setMinimum(0)
            self.pgb.setMaximum(100)
            self.pgb.setValue(self.pv)
            self.pgb.setFormat('Loaded  %p%'.format(self.pgb.value() - self.pgb.minimum()))
            self.horizontalLayout_b.addWidget(self.pgb)

            # space
            spacerItem = QtWidgets.QSpacerItem(3, 20, QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Minimum)
            self.horizontalLayout_b.addItem(spacerItem)

            m_list = []
            if self.ckb1.isChecked():
                m_list.append('apriori')
            if self.ckb2.isChecked():
                m_list.append('mapriori')
            if self.ckb3.isChecked():
                m_list.append('maxminer')
            if self.ckb4.isChecked():
                m_list.append('hmine')

            self.pushButton_3 = QtWidgets.QPushButton(self.widget)
            self.pushButton_3.setObjectName("pushButton_3")
            self.horizontalLayout_b.addWidget(self.pushButton_3)
            self.pushButton_3.clicked.connect(
                lambda: self.attack_pm(time.time(), m_list, self.input_1.text(),
                                    self.input_2.text(), self.input_3.text(), self.input_4.text(),
                                    self.cb2.currentText(), self.cb3.currentText(), self.input_5.text()))


            self.pushButton_3.setStyleSheet(''' text-align : center;
                                                  background-color : #009688;
                                                  height : 80px;
                                                  width: 170px;
                                                  border-style: outset;
                                                  border-radius: 100px;
                                                  color: #fff;
                                                  font : 26px  ''')

            # text browser
            self.verticalLayout.addWidget(self.widget)
            self.verticalLayout_p.addWidget(self.widget_p)
            self.verticalLayout_b.addWidget(self.widget_b)
            self.textBrowserWidget = QtWidgets.QTextBrowser()
            self.textBrowserWidget.setObjectName("textBrowserWidget")
            self.verticalLayout_p.addWidget(self.textBrowserWidget)

            # set shown values
            _translate = QtCore.QCoreApplication.translate
            self.label.setText(_translate("Form", "pattern_mine method"))
            self.label_2.setText(_translate("Form", "stop_iter_perc"))
            self.label_3.setText(_translate("Form", "stop_iter_perc_lm"))
            self.label_4.setText(_translate("Form", "min_part_size"))
            self.label_5.setText(_translate("Form", "max_num_many"))
            self.label_6.setText(_translate("Form", "lang_model_min_freq"))
            self.pushButton_3.setText(_translate("Form", "Start Attack"))
            self.textBrowserWidget.setHtml(_translate("Form",
                                                      "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
                                                      "<html><head><meta name=\"qrichtext\" content=\"1\" /><style type=\"text/css\">\n"
                                                      "p, li { white-space: pre-wrap; }\n"
                                                      "</style></head><body style=\" font-family:\'SimSun\'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:18pt; font-weight:600; color:#00aaff;\">Pattern mining based attack</span></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><a href=\"https://ieeexplore.ieee.org/abstract/document/8731536\"><span style=\" text-decoration: underline; color:#0000ff;\">Paper URL</span></a></p>\n"
                                                      "<p style=\"-qt-paragraph-type:empty; margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px; text-decoration: underline; color:#0000ff;\"><br /></p>\n"
                                                      "<p style=\"-qt-paragraph-type:empty; margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px; text-decoration: underline; color:#0000ff;\"><br /></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'HelveticaNeue Regular\',\'sans-serif\'; font-size:18px; font-weight:696; color:#00aaff; background-color:#ffffff;\">Abstract:</span></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px; background-color:#ffffff;\"><span style=\" font-family:\'HelveticaNeue Regular\',\'sans-serif\'; font-size:10pt; color:#333333; background-color:#ffffff;\">Privacy-preserving record linkage (PPRL) is the process of identifying records that correspond to the same entities across several databases without revealing any sensitive information about these entities. One popular PPRL technique is Bloom filter (BF) encoding, with first applications of BF based PPRL now being employed in real-world linkage applications. Here we present a cryptanalysis attack that can re-identify attribute values encoded in BFs. Our method applies maximal frequent itemset mining on a BF database to first identify sets of frequently co-occurring bit positions that correspond to encoded frequent q-grams (character substrings extracted from plain-text values). Using a language model, we then identify additional q-grams by applying pattern mining on subsets of BFs that encode a previously identified frequent q-gram. Experiments on a real database show that our attack can successfully re-identify sensitive values even when each BF in a database is unique.</span></p>\n"
                                                      "<p style=\"-qt-paragraph-type:empty; margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px; font-size:12pt; font-weight:600; color:#00aaff;\"><br /></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:12pt; font-weight:600; color:#00aaff;\">Attack Process Info:</span></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'NimbusRomNo9L-Medi\'; font-size:9.46485pt; font-weight:600; color:#000000;\">Step 1: Identifying Co-occurring Bit Positions</span></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'NimbusRomNo9L-Medi\'; font-size:9.46485pt; font-weight:600; color:#000000;\">Step 2: Language Model Based Q-gram Set Expansion</span> </p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'NimbusRomNo9L-Medi\'; font-size:9.46485pt; font-weight:600; color:#000000;\">Step 3: Plain-text Value Re-identifification</span> </p>\n"
                                                      "<p style=\"-qt-paragraph-type:empty; margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><br /></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:12pt; font-weight:600; color:#00aaff;\">Parameters detail:</span><span style=\" font-weight:600;\"> </span></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; font-weight:600; color:#000000;\">pattern_mine_method_str: </span><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">  </span></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">The name of the algorithm use for pattern mining,<br />where possible values are:<br />   - apriori   Classical breath-first Apriori<br />   - mapriori  Memory-based Apriori<br />   - maxminer  The breath-first Max-Minor approach<br />   - hmine</span></p>\n"
                                                      "<p style=\"-qt-paragraph-type:empty; margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px; font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\"><br /></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; font-weight:600; color:#000000;\">stop_iter_perc:</span><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">         </span></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">The minimum percentage difference required between<br />the two most frequent q-grams to continue the<br />recursive Apriori pattern mining approach</span></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\"><br /></span><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; font-weight:600; color:#000000;\">stop_iter_perc_lm: </span><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">        </span></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">The minimum percentage difference required between<br />the two q-grams with highest condional probabilities<br />in language model</span></p>\n"
                                                      "<p style=\"-qt-paragraph-type:empty; margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px; font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\"><br /></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; font-weight:600; color:#000000;\">min_part_size:</span><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">             </span></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">The minimum number of BFs in a \'partition\' for the<br />partition to be used with the Apriori algorithm</span></p>\n"
                                                      "<p style=\"-qt-paragraph-type:empty; margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px; font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\"><br /></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; font-weight:600; color:#000000;\">max_num_many: </span><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">             </span></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">For the re-identification step, the maximum number<br />of 1-to-many matches to consider</span></p>\n"
                                                      "<p style=\"-qt-paragraph-type:empty; margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px; font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\"><br /></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; font-weight:600; color:#000000;\">re_id_method: </span><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">             </span></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">The approach to be used for re-identification, </span></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">with possible values: </span></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">   -\'set_inter\'</span></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">   -\'apriori\'<br />   -\'q_gram_tuple\' </span></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">   -\'bf_q_gram_tuple\' </span></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">   -\'bf_tuple\'<br />   -\'all\'</span></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">   -\'none\' (if set to \'none\' then no<br />    re-identification will be attempted)<br /></span></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; font-weight:600; color:#000000;\">expand_lang_model: </span><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">        </span></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">expand lang modelis the language model type. </span></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">Inputs can be:<br />   - single<br />   - tuple<br />   - all</span></p>\n"
                                                      "<p style=\"-qt-paragraph-type:empty; margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px; font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\"><br /></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; font-weight:600; color:#000000;\">lang_model_min_freq:</span></p>\n"
                                                      "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">minimum frequency of language model</span></p></body></html>"))

        # -----------------------------------------------------------------------
        if value == "bit pattern frequency based":
            # bit pattern frequency based attack parameters
            # param_1 : min_freq
            self.label = QtWidgets.QLabel(self.widget)
            font = QtGui.QFont()
            font.setPointSize(8)
            self.label.setFont(font)
            self.label.setObjectName("label")
            self.label.setToolTip("is the minimum frequency of Bloom filters and attribute \n"
                                  "values to consider in the analysis")
            self.label.setToolTipDuration(3000)
            self.horizontalLayout.addWidget(self.label)

            self.input_1 = QtWidgets.QLineEdit(self.widget)
            self.input_1.setObjectName("input_1")
            self.input_1.setText("100")
            self.horizontalLayout.addWidget(self.input_1)

            # space
            spacerItem = QtWidgets.QSpacerItem(1, 20, QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Minimum)
            self.horizontalLayout.addItem(spacerItem)

            # num_freq_attr_val_list
            self.label_2 = QtWidgets.QLabel(self.widget)
            self.label_2.setObjectName("label_2")
            self.label_2.setToolTip("is a list with the numbers of most frequent\n"
                                    "attribute values from the analysis file we aim to\n"
                                    "re-identify.\n")
            self.label_2.setToolTipDuration(3000)
            self.horizontalLayout.addWidget(self.label_2)
            self.input_2 = QtWidgets.QLineEdit(self.widget)
            self.input_2.setObjectName("input_2")
            self.input_2.setText("[100,50,20,10]")
            self.horizontalLayout.addWidget(self.input_2)
            self.input_2.setStyleSheet(''' height : 30px;
                                                         border-style: outset;
                                                         padding-left: 5px;
                                                         border: 1px solid #ccc;
                                                         border-radius: 5px;
                                                         font : 12px  ''')

            # space
            spacerItem = QtWidgets.QSpacerItem(1, 20, QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Minimum)
            self.horizontalLayout.addItem(spacerItem)

            # space
            spacerItem = QtWidgets.QSpacerItem(2, 20, QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Minimum)
            self.horizontalLayout_b.addItem(spacerItem)

            # Progress bar
            self.pgb = QtWidgets.QProgressBar(self.widget)
            self.pgb.move(50, 50)
            self.pgb.resize(250, 20)
            self.pgb.setStyleSheet(
                "QProgressBar { border: 2px solid grey; border-radius: 5px; color: rgb(20,20,20);  background-color: "
                "#FFFFFF; text-align: center;}QProgressBar::chunk {background-color: rgb(100,200,200); border-radius: "
                "10px; margin: 0.1px;  width: 1px;}")

            font = QFont()
            font.setBold(True)
            font.setWeight(30)
            self.pgb.setFont(font)
            self.pv = 0
            self.pgb.setMinimum(0)
            self.pgb.setMaximum(100)
            self.pgb.setValue(self.pv)
            self.pgb.setFormat('Loaded  %p%'.format(self.pgb.value() - self.pgb.minimum()))
            self.horizontalLayout_b.addWidget(self.pgb)

            # space
            spacerItem = QtWidgets.QSpacerItem(3, 20, QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Minimum)
            self.horizontalLayout_b.addItem(spacerItem)

            self.pushButton_3 = QtWidgets.QPushButton(self.widget)
            self.pushButton_3.setObjectName("pushButton_3")
            self.horizontalLayout_b.addWidget(self.pushButton_3)
            self.pushButton_3.clicked.connect(
                lambda: self.attack_bpf(time.time(), self.input_1.text(), self.input_2.text()))

            self.pushButton_3.setStyleSheet(''' text-align : center;
                                                  background-color : #009688;
                                                  height : 80px;
                                                  width: 170px;
                                                  border-style: outset;
                                                  border-radius: 100px;
                                                  color: #fff;
                                                  font : 26px  ''')

            # text browser
            self.verticalLayout.addWidget(self.widget)
            self.verticalLayout_p.addWidget(self.widget_p)
            self.verticalLayout_b.addWidget(self.widget_b)
            self.textBrowserWidget = QtWidgets.QTextBrowser()
            self.textBrowserWidget.setObjectName("textBrowserWidget")
            self.verticalLayout_p.addWidget(self.textBrowserWidget)

            # set shown values
            _translate = QtCore.QCoreApplication.translate
            self.label.setText(_translate("Form", "minimum frequency"))
            self.label_2.setText(_translate("Form", "most frequent attribute values list"))
            self.pushButton_3.setText(_translate("Form", "Start Attack"))
            self.textBrowserWidget.setHtml(_translate("Form",
                                            "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
                                            "<html><head><meta name=\"qrichtext\" content=\"1\" /><style type=\"text/css\">\n"
                                            "p, li { white-space: pre-wrap; }\n"
                                            "</style></head><body style=\" font-family:\'SimSun\'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:18pt; font-weight:600; color:#00aaff;\">Bit Pattern Frequency based attack</span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><a href=\"https://link.springer.com/chapter/10.1007/978-3-319-57454-7_49\"><span style=\" text-decoration: underline; color:#0000ff;\">Paper URL</span></a></p>\n"
                                            "<p style=\"-qt-paragraph-type:empty; margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px; text-decoration: underline; color:#0000ff;\"><br /></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'HelveticaNeue Regular\',\'sans-serif\'; font-size:18px; font-weight:696; color:#00aaff; background-color:#ffffff;\">Abstract:</span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px; background-color:#ffffff;\"><span style=\" font-family:\'TkfqsvRtmjjlCMR9\'; font-size:8.9664pt; color:#000000;\">Privacy-preserving record linkage (PPRL) is the process of </span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'TkfqsvRtmjjlCMR9\'; font-size:8.9664pt; color:#000000;\">identifying records that represent the same entity across databases held </span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'TkfqsvRtmjjlCMR9\'; font-size:8.9664pt; color:#000000;\">by difffferent organizations without revealing any sensitive information </span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'TkfqsvRtmjjlCMR9\'; font-size:8.9664pt; color:#000000;\">about these entities. A popular technique used in PPRL is Bloom fifilter </span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'TkfqsvRtmjjlCMR9\'; font-size:8.9664pt; color:#000000;\">encoding, which has shown to be an effiffifficient and effffective way to encode </span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'TkfqsvRtmjjlCMR9\'; font-size:8.9664pt; color:#000000;\">sensitive information into bit vectors while still enabling approximate </span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'TkfqsvRtmjjlCMR9\'; font-size:8.9664pt; color:#000000;\">matching of attribute values. However, the encoded values in Bloom fifil</span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'TkfqsvRtmjjlCMR9\'; font-size:8.9664pt; color:#000000;\">ters are vulnerable to cryptanalysis attacks. Under specifific conditions, </span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'TkfqsvRtmjjlCMR9\'; font-size:8.9664pt; color:#000000;\">these attacks are successful in that some frequent sensitive attribute val</span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'TkfqsvRtmjjlCMR9\'; font-size:8.9664pt; color:#000000;\">ues can be re-identifified. In this paper we propose and evaluate on real </span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'TkfqsvRtmjjlCMR9\'; font-size:8.9664pt; color:#000000;\">databases a novel effiffifficient attack on Bloom fifilters. </span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'TkfqsvRtmjjlCMR9\'; font-size:8.9664pt; color:#000000;\">Our approach is based on the construction principle of Bloom fifilters of hashing elements of sets into bit positions. The attack is independent of the encoding function and its parameters used, it can correctly re-identify sensitive attribute values even when various recently proposed hardening techniques have </span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'TkfqsvRtmjjlCMR9\'; font-size:8.9664pt; color:#000000;\">been applied, and it runs in a few seconds instead of hours.</span> </p>\n"
                                            "<p style=\"-qt-paragraph-type:empty; margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px; font-size:12pt; font-weight:600; color:#00aaff;\"><br /></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:12pt; font-weight:600; color:#00aaff;\">Attack Process Info:</span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'NimbusRomNo9L-Medi\'; font-size:9.46485pt; font-weight:600; color:#000000;\">Step 1: </span><span style=\" font-family:\'DdxfhcPgdkchCMBX10\'; font-size:9.9626pt; font-weight:600; color:#000000;\">Candidate Q-Gram Set Generation</span> </p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'NimbusRomNo9L-Medi\'; font-size:9.46485pt; font-weight:600; color:#000000;\">Step 2: </span><span style=\" font-family:\'DdxfhcPgdkchCMBX10\'; font-size:9.9626pt; font-weight:600; color:#000000;\">Attribute Value Re-identifification</span> </p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'NimbusRomNo9L-Medi\'; font-size:9.46485pt; font-weight:600; color:#000000;\">Step 3: </span><span style=\" font-family:\'DdxfhcPgdkchCMBX10\'; font-size:9.9626pt; font-weight:600; color:#000000;\">Analysis and Limitations</span> </p>\n"
                                            "<p style=\"-qt-paragraph-type:empty; margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><br /></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:12pt; font-weight:600; color:#00aaff;\">Parameters detail:</span><span style=\" font-weight:600;\"> </span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; font-weight:600; color:#000000;\">min_freq: </span><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">  </span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">is the minimum frequency of Bloom filters and<br />attribute values to consider in the analysis</span></p>\n"
                                            "<p style=\"-qt-paragraph-type:empty; margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px; font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\"><br /></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; font-weight:600; color:#000000;\">num_freq_attr_val_list</span><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#808080;\">:  </span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-family:\'JetBrains Mono\',\'monospace\'; font-size:9.8pt; color:#000000;\">is a list with the numbers of most frequent<br />attribute values from the analysis file we aim to<br />re-identify</span></p>\n"
                                            "<p style=\"-qt-paragraph-type:empty; margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><br /></p></body></html>"))

        return self.right_widget

    # evaluation manager
    def evaluation_management(self):
        global result_name_list
        if self.right_widget:
            self.main_layout.removeWidget(self.right_widget)  # remove exist right widget
        self.setWindowTitle('attack simulator - evaluation')
        self.setLeftMenu(self.left_button_4)  # select button effect
        self.right_widget = QtWidgets.QWidget()  # create new right widget
        self.right_widget.setObjectName('right_widget')
        self.verticalLayout = QtWidgets.QVBoxLayout()
        self.verticalLayout.setObjectName("verticalLayout")

        self.right_layout = self.verticalLayout
        self.right_widget.setLayout(self.right_layout)  # set right widget to layout

        # right_widget is beginning at row 0, column 2, take 12 rows, 10 columns
        self.main_layout.addWidget(self.right_widget, 0, 2, 12, 10)

        self.widget = QtWidgets.QWidget()
        self.horizontalLayout = QtWidgets.QHBoxLayout(self.widget)
        self.horizontalLayout.setObjectName("horizontalLayout")
        self.label = QtWidgets.QLabel(self.widget)
        font = QtGui.QFont()
        font.setPointSize(12)
        self.label.setFont(font)
        self.label.setObjectName("label")
        self.horizontalLayout.addWidget(self.label)

        # encode dataset comboBox1
        self.cb1 = QComboBox(self)
        # fill the comboBox
        print(result_name_list)
        for result in result_name_list:
            self.cb1.addItem(str(result))
        self.cb1.currentIndexChanged[int].connect(lambda: self.getResultList(self.cb1.currentText()))
        self.cb1.setStyleSheet(''' text-align : center;
                                                      height : 50px;
                                                      padding-left: 10px;
                                                      font : 24px  ''')
        self.horizontalLayout.addWidget(self.cb1)
        # delete dataset
        self.pushButton_del = QtWidgets.QPushButton(self.widget)
        self.pushButton_del.setObjectName("pushButton_del")
        self.horizontalLayout.addWidget(self.pushButton_del)
        self.pushButton_del.clicked.connect(lambda: self.dataDelete(self.cb1.currentText()))
        self.pushButton_del.setStyleSheet(''' text-align : center;
                                                      background-color : #f44336;
                                                      height : 60px;
                                                      width: 160px;
                                                      border-style: outset;
                                                      border-radius: 50px;
                                                      color: #fff;
                                                      font : 22px  ''')

        # space
        spacerItem = QtWidgets.QSpacerItem(40, 20, QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Minimum)
        self.horizontalLayout.addItem(spacerItem)

        # import dataset
        self.pushButton_3 = QtWidgets.QPushButton(self.widget)
        self.pushButton_3.setObjectName("pushButton")
        self.horizontalLayout.addWidget(self.pushButton_3)
        self.pushButton_3.clicked.connect(lambda: self.open_file())
        self.pushButton_3.setStyleSheet(''' text-align : center;
                                                      background-color : #009688;
                                                      height : 80px;
                                                      width: 170px;
                                                      border-style: outset;
                                                      border-radius: 100px;
                                                      color: #fff;
                                                      font : 26px  ''')

        # table form
        self.verticalLayout.addWidget(self.widget)
        self.tableWidget = QtWidgets.QTableWidget()
        self.tableWidget.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectRows)
        self.tableWidget.setObjectName("tableWidget")
        self.verticalLayout.addWidget(self.tableWidget)

        # set shown values
        _translate = QtCore.QCoreApplication.translate
        self.label.setText(_translate("Form", "select Attack Result:"))
        self.pushButton_del.setText(_translate("Form", "Delete Result"))
        self.pushButton_3.setText(_translate("Form", "import new"))

        if len(result_name_list) > 1:
            self.cb1.setCurrentIndex(1)
            self.getResultList(self.cb1.currentText())

        return self.right_widget

    # comparison tools
    def comparison(self):

        return self.right_widget

    # guide page
    def guide(self):
        global dataset_names_list
        if self.right_widget:
            self.main_layout.removeWidget(self.right_widget)  # remove exist right widget
        self.setWindowTitle('attack simulator - Guide Book')
        self.setLeftMenu(self.left_button_9)  # select button effect
        self.right_widget = QtWidgets.QWidget()  # create new right widget
        self.right_widget.setObjectName('right_widget')
        self.verticalLayout = QtWidgets.QVBoxLayout()
        self.verticalLayout.setObjectName("verticalLayout")

        self.right_layout = self.verticalLayout
        self.right_widget.setLayout(self.right_layout)  # set right widget to layout

        # right_widget is beginning at row 0, column 2, take 12 rows, 10 columns
        self.main_layout.addWidget(self.right_widget, 0, 2, 12, 10)

        self.widget = QtWidgets.QWidget()
        self.horizontalLayout = QtWidgets.QHBoxLayout(self.widget)
        self.horizontalLayout.setObjectName("horizontalLayout")

        # space
        spacerItem = QtWidgets.QSpacerItem(40, 20, QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Minimum)
        self.horizontalLayout.addItem(spacerItem)

        # begin button
        self.pushButton_begin = QtWidgets.QPushButton(self.widget)
        self.pushButton_begin.setObjectName("pushButton")
        self.horizontalLayout.addWidget(self.pushButton_begin)
        self.pushButton_begin.clicked.connect(lambda: self.setRightWidget(flag=C.FLAG_DATASET))
        self.pushButton_begin.setStyleSheet(''' text-align : center;
                                              background-color : #009688;
                                              height : 80px;
                                              width: 180px;
                                              border-style: outset;
                                              border-radius: 100px;
                                              color: #fff;
                                              font : 26px  ''')

        # text Browser
        self.textBrowser = QtWidgets.QTextBrowser(self.widget)
        self.textBrowser.setObjectName("textBrowser")
        self.verticalLayout.addWidget(self.textBrowser)

        # set shown values
        _translate = QtCore.QCoreApplication.translate
        self.pushButton_begin.setText(_translate("Form", "Start!"))
        self.textBrowser.setHtml(_translate("Form",
                                            "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
                                            "<html><head><meta name=\"qrichtext\" content=\"1\" /><style type=\"text/css\">\n"
                                            "p, li { white-space: pre-wrap; }\n"
                                            "</style></head><body style=\" font-family:\'SimSun\'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:18pt; font-weight:600; color:#00aaff;\">Welcome to use PPRL attack simulator</span></p>\n"
                                            "<p style=\"-qt-paragraph-type:empty; margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px; font-size:14pt; font-weight:600; color:#00aaff;\"><br /></p>\n"
                                            "<p style=\"-qt-paragraph-type:empty; margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px; font-size:14pt; font-weight:600; color:#00aaff;\"><br /></p>\n"
                                            "<p style=\"-qt-paragraph-type:empty; margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px; font-size:14pt; font-weight:600; color:#00aaff;\"><br /></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:14pt; font-weight:600; font-style:italic; color:#000000;\">part1 introduction</span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:12pt; font-weight:600; color:#000000;\">This tools is aiming to simulate different privacy-preserving record linkage attacks on your chosen dataset. It could help you to test robust and safty risk of dataset.</span></p>\n"
                                            "<p style=\"-qt-paragraph-type:empty; margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px; font-size:12pt; font-weight:600; color:#000000;\"><br /></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:14pt; font-weight:600; font-style:italic; color:#000000;\">part2 general flow</span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:11pt; font-weight:600; color:#000000;\">dataset manage</span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:12pt; font-weight:600; color:#000000;\">You could begin at dataset choosing.</span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:12pt; font-weight:600; color:#000000;\">First, you need to go to the dataset page on the top left.</span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:12pt; font-weight:600; color:#000000;\">Then, you could use the combobox to check the ready dataset. You could use our default dataset to familiar with our tools, or import your own datasets by the import button.</span></p>\n"
                                            "<p style=\"-qt-paragraph-type:empty; margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px; font-size:12pt; font-weight:600; color:#000000;\"><br /></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:11pt; font-weight:600; color:#000000;\">encode manage</span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:12pt; font-weight:600; color:#000000;\">After check and prepare needed dataset, we next go to encode page on the left bar.</span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:12pt; font-weight:600; color:#000000;\">First, you need to choose a encoding methods.</span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:12pt; font-weight:600; color:#000000;\">Then, it will go to the corresponding encode parameters page. Here you need to choose:</span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:12pt; font-weight:600; color:#000000;\">1.encode dataset</span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:12pt; font-weight:600; color:#000000;\">2.plaintext dataset</span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:12pt; font-weight:600; color:#000000;\">3.attributes to be encoded</span></p>\n"
                                            "<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:12pt; font-weight:600; color:#000000;\">4.encoding parameters </span></p>\n"
                                            "<p style=\"-qt-paragraph-type:empty; margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px; font-size:12pt; font-weight:600; color:#00aaff;\"><br /></p></body></html>"))

        self.verticalLayout.addWidget(self.widget)
        return self.right_widget

    # delete dataset in dataset manager
    def dataDelete(self, dataset_name):
        if dataset_name == 'select a dataset':
            QMessageBox.information(self, 'error', "please select a dataset to delete")
            return
        del datasets[dataset_name]
        # fresh the comboBox of dataset
        self.setRightWidget()
        QMessageBox.information(self, 'message', "dataset deleted successfully!")

    # update table
    def getDataList(self, dataset_name, flag, dataset):
        current_data = datasets[dataset_name]
        self.addTableRow(current_data, flag, dataset)

    # add contents to the table
    def addTableRow(self, data, flag, dataset):
        global encode_header_combobox, plain_header_combobox, class_dict
        if dataset == 0:
            self.tableWidget.setRowCount(0)
            if len(data) == 0:
                self.tableWidget.setRowCount(1)
                item = QTableWidgetItem()
                item.setTextAlignment(QtCore.Qt.AlignCenter)
                item.setText("无数据")
                self.tableWidget.setItem(0, 0, item)
                return

            self.tableWidget.setRowCount(data.shape[0] + 1)
            self.tableWidget.setColumnCount(data.shape[1])

            # table column name
            _translate = QtCore.QCoreApplication.translate
            column_name_list = list(data.columns)
            for i in range(len(column_name_list)):
                item = QtWidgets.QTableWidgetItem()
                self.tableWidget.setHorizontalHeaderItem(i, item)
                if flag == C.FLAG_ENCODING:
                    checkbox1 = QtWidgets.QCheckBox()
                    encode_header_combobox.append(checkbox1)
                    hLayout = QtWidgets.QFormLayout()
                    hLayout.addWidget(checkbox1)
                    hLayout.setAlignment(checkbox1, QtCore.Qt.AlignCenter)
                    widget = QtWidgets.QWidget()
                    widget.setLayout(hLayout)
                    self.tableWidget.setCellWidget(0, i, widget)
                    self.tableWidget.setRowHeight(0, 50)
            self.verticalLayout.addWidget(self.tableWidget)
            for i in range(len(column_name_list)):
                item = self.tableWidget.horizontalHeaderItem(i)
                item.setText(_translate("Form", column_name_list[i]))

            for i in range(data.shape[0]):
                for j in range(data.shape[1]):
                    item = QTableWidgetItem(str(data.iloc[i, j]))
                    item.setTextAlignment(QtCore.Qt.AlignCenter)
                    item.setFlags(QtCore.Qt.ItemIsEnabled)
                    self.tableWidget.setItem(i + 1, j, item)

        elif dataset == 1:
            self.tableWidget_p.setRowCount(0)
            if len(data) == 0:
                self.tableWidget_p.setRowCount(1)
                item = QTableWidgetItem()
                item.setTextAlignment(QtCore.Qt.AlignCenter)
                item.setText("无数据")
                self.tableWidget_p.setItem(0, 0, item)
                return

            self.tableWidget_p.setRowCount(data.shape[0] + 1)
            self.tableWidget_p.setColumnCount(data.shape[1])

            # table column name
            _translate = QtCore.QCoreApplication.translate
            column_name_list = list(data.columns)
            for i in range(len(column_name_list)):
                item = QtWidgets.QTableWidgetItem()
                self.tableWidget_p.setHorizontalHeaderItem(i, item)
                if flag == C.FLAG_ENCODING:
                    checkbox1 = QtWidgets.QCheckBox()
                    plain_header_combobox.append(checkbox1)
                    hLayout = QtWidgets.QFormLayout()
                    hLayout.addWidget(checkbox1)
                    hLayout.setAlignment(checkbox1, QtCore.Qt.AlignCenter)
                    widget = QtWidgets.QWidget()
                    widget.setLayout(hLayout)
                    self.tableWidget_p.setCellWidget(0, i, widget)
                    self.tableWidget_p.setRowHeight(0, 50)
            self.verticalLayout_p.addWidget(self.tableWidget_p)
            for i in range(len(column_name_list)):
                item = self.tableWidget_p.horizontalHeaderItem(i)
                item.setText(_translate("Form", column_name_list[i]))

            for i in range(data.shape[0]):
                for j in range(data.shape[1]):
                    item = QTableWidgetItem(str(data.iloc[i, j]))
                    item.setTextAlignment(QtCore.Qt.AlignCenter)
                    item.setFlags(QtCore.Qt.ItemIsEnabled)
                    self.tableWidget_p.setItem(i + 1, j, item)

    # get selected attributes
    def getAttriList(self, dataset):
        global encode_header_combobox, plain_header_combobox
        if dataset == 0:
            encode_ids = []
            for i in range(len(encode_header_combobox)):
                try:
                    if encode_header_combobox[i].checkState() == 2:
                        # encode_ids.append(str(self.tableWidget.horizontalHeaderItem(i).text()))
                        encode_ids.append(i)
                except Exception as e:
                    print(e)
            if len(encode_ids) == 0:
                QMessageBox.information(self, 'ERROR', "Please select encode set attribute!")
            return encode_ids
        elif dataset == 1:
            plain_ids = []
            for i in range(len(plain_header_combobox)):
                try:
                    if plain_header_combobox[i].checkState() == 2:
                        plain_ids.append(i)
                except Exception as e:
                    print(e)
            if len(plain_ids) == 0:
                QMessageBox.information(self, 'ERROR', "Please select plain set attribute!")
            return plain_ids

    # get all datasets name
    def getDatasetNameList(self, name=''):
        global datasets
        print("get dataset name list")
        return list(datasets.keys())

    # open dataset in dataset manager
    def open_file(self):
        global datasets
        print("choose dataset")
        QMessageBox.information(self, 'IMPORT DATASET',
                                "Please select your dataset (csv format only!)\n your data should have a head line!")
        fileName, fileType = QtWidgets.QFileDialog.getOpenFileName(self, "select file", os.getcwd() + '/data',
                                                                   "CSV Files(*.csv)")
        if fileName == '':
            return

        data = pd.read_csv(fileName)
        datasets[fileName] = data

        # fresh the comboBox of dataset
        self.setRightWidget(C.FLAG_DATASET)

    def setLeftMenu(self, button):
        global activat_menu
        if activat_menu != None:
            activat_menu.setStyleSheet('''
                        width:30px;
                        font-size:25px;
                        ''')
        activat_menu = button
        button.setStyleSheet('''
                    width:20px;
                    font-size:18px;
                    border-left:4px solid #00bcd4;
                    font-weight:700;
                    ''')

    def encoded_check(self, encode_bf_dict):
        if self.right_widget:
            self.main_layout.removeWidget(self.right_widget)  # remove exist right widget

        self.right_widget = QtWidgets.QWidget()  # create new right widget
        self.right_widget.setObjectName('right_widget')
        self.verticalLayout = QtWidgets.QVBoxLayout()
        self.verticalLayout.setObjectName("verticalLayout")

        self.right_layout = self.verticalLayout
        self.right_widget.setLayout(self.right_layout)  # set right widget to layout

        # right_widget is beginning at row 0, column 2, take 12 rows, 10 columns
        self.main_layout.addWidget(self.right_widget, 0, 2, 12, 10)
        self.widget = QtWidgets.QWidget()
        self.horizontalLayout = QtWidgets.QHBoxLayout(self.widget)
        self.horizontalLayout.setObjectName("horizontalLayout")

        # reset encode process
        self.pushButton_del = QtWidgets.QPushButton(self.widget)
        self.pushButton_del.setObjectName("pushButton_del")
        self.horizontalLayout.addWidget(self.pushButton_del)
        self.pushButton_del.clicked.connect(lambda: self.setRightWidget(self, flag=C.FLAG_ENCODING))
        self.pushButton_del.setStyleSheet(''' text-align : center;
                                                      background-color : #f44336;
                                                      height : 60px;
                                                      width: 160px;
                                                      border-style: outset;
                                                      border-radius: 50px;
                                                      color: #fff;
                                                      font : 22px  ''')

        # space
        spacerItem = QtWidgets.QSpacerItem(40, 20, QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Minimum)
        self.horizontalLayout.addItem(spacerItem)

        self.label = QtWidgets.QLabel(self.widget)
        font = QtGui.QFont()
        font.setPointSize(26)
        self.label.setFont(font)
        self.label.setObjectName("label")
        self.horizontalLayout.addWidget(self.label)

        # space1
        spacerItem1 = QtWidgets.QSpacerItem(40, 20, QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Minimum)
        self.horizontalLayout.addItem(spacerItem1)

        # attack dataset
        self.pushButton_3 = QtWidgets.QPushButton(self.widget)
        self.pushButton_3.setObjectName("pushButton")
        self.horizontalLayout.addWidget(self.pushButton_3)
        self.pushButton_3.clicked.connect(lambda: self.setRightWidget(flag=C.FLAG_ATTACK))
        self.pushButton_3.setStyleSheet(''' text-align : center;
                                                      background-color : #009688;
                                                      height : 80px;
                                                      width: 170px;
                                                      border-style: outset;
                                                      border-radius: 100px;
                                                      color: #fff;
                                                      font : 26px  ''')

        # table form
        self.verticalLayout.addWidget(self.widget)
        self.tableWidget = QtWidgets.QTableWidget()
        self.tableWidget.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectRows)
        self.tableWidget.setObjectName("tableWidget")
        self.verticalLayout.addWidget(self.tableWidget)

        view_len = max(20, len(encode_bf_dict))
        self.tableWidget.setRowCount(view_len)
        self.tableWidget.setColumnCount(1)
        self.tableWidget.setColumnWidth(0, 1500)
        i = 0
        for v in encode_bf_dict.values():
            item = QTableWidgetItem(str(v))
            item.setTextAlignment(QtCore.Qt.AlignCenter)
            item.setFlags(QtCore.Qt.ItemIsEnabled)
            self.tableWidget.setItem(i, 0, item)
            i += 1
            if i > view_len:
                break

        # set shown values
        _translate = QtCore.QCoreApplication.translate
        self.label.setText(_translate("Form", "Encoding result view"))
        self.pushButton_del.setText(_translate("Form", "Back and Reset"))
        self.pushButton_3.setText(_translate("Form", "Next step"))

        return self.right_widget

    # encode function for BF encoding
    def encode(self, encode_data_set_name, plain_data_set_name, q, hash_type, num_hash_funct, bf_len, bf_harden,
               encode_attr_list, plain_attr_list, bf_encode,
               encode_col_sep_char, plain_col_sep_char, enc_param_list, harden_param_list):
        global pm_dict
        encode_header_line_flag = True
        encode_rec_id_col = 0
        plain_rec_id_col = 0
        plain_header_line_flag = True
        padded = False
        # valid value check
        q = int(q)
        assert q >= 1, q
        assert hash_type in ['dh', 'rh', 'edh', 'th'], hash_type

        if num_hash_funct == 'opt':
            assert num_hash_funct == 'opt', num_hash_funct
        else:
            num_hash_funct = int(num_hash_funct)
            assert num_hash_funct >= 1, num_hash_funct
        bf_len = int(bf_len)
        assert bf_len > 1, bf_len
        assert bf_harden in ['none', 'balance', 'fold', 'rule90', 'mchain', 'salt'], \
            bf_harden

        #
        assert encode_rec_id_col >= 0, encode_rec_id_col
        assert encode_header_line_flag in [True, False], encode_header_line_flag
        assert isinstance(encode_attr_list, list), encode_attr_list

        assert plain_rec_id_col >= 0, plain_rec_id_col
        assert plain_header_line_flag in [True, False], plain_header_line_flag
        assert isinstance(plain_attr_list, list), plain_attr_list

        #
        assert bf_encode in ['abf', 'clk', 'rbf-s', 'clkrbf'], bf_encode
        #
        assert padded in [True, False], padded

        if (bf_harden == 'mchain'):
            mc_chain_len = harden_param_list[0]
            mc_sel_method = harden_param_list[1]
        else:
            mc_chain_len = 'None'
            mc_sel_method = 'None'

        if (bf_harden == 'fold'):
            if (bf_len % 2 != 0):
                raise Exception('BF hardening approach "fold" needs an even BF length')

        if (len(encode_col_sep_char) > 1):
            if (encode_col_sep_char == 'tab'):
                encode_col_sep_char = '\t'
            elif (encode_col_sep_char[0] == '"') and (encode_col_sep_char[-1] == '"') \
                    and (len(encode_col_sep_char) == 3):
                encode_col_sep_char = encode_col_sep_char[1]
            else:
                print('Illegal encode data set column separator format:', \
                      encode_col_sep_char)

        if (len(plain_col_sep_char) > 1):
            if (plain_col_sep_char == 'tab'):
                plain_col_sep_char = '\t'
            elif (plain_col_sep_char[0] == '"') and \
                    (plain_col_sep_char[-1] == '"') and \
                    (len(plain_col_sep_char) == 3):
                plain_col_sep_char = plain_col_sep_char[1]
            else:
                print('Illegal plain text data set column separator format:', \
                      plain_col_sep_char)

        # file for saving
        encode_base_data_set_name = encode_data_set_name.split('/')[-1]
        encode_base_data_set_name = encode_base_data_set_name.replace('.csv', '')
        encode_base_data_set_name = encode_base_data_set_name.replace('.gz', '')
        assert ',' not in encode_base_data_set_name

        plain_base_data_set_name = plain_data_set_name.split('/')[-1]
        plain_base_data_set_name = plain_base_data_set_name.replace('.csv', '')
        plain_base_data_set_name = plain_base_data_set_name.replace('.gz', '')
        assert ',' not in plain_base_data_set_name

        # file name
        res_file_name = 'bf-attack-col-pattern-results-%s-%s-%s.csv' % \
                        (encode_base_data_set_name, plain_base_data_set_name, \
                         time.strftime("%Y%m%d-%H-%M-%S", time.localtime()))
        print()
        print('Write results into file:', res_file_name)
        print()
        print('-' * 80)
        print()

        # Step 1: Load the data sets and extract q-grams for selected attributes

        # Check if same data sets and same attributes were given
        #
        if ((encode_data_set_name == plain_data_set_name) and \
                (encode_attr_list == plain_attr_list)):
            same_data_attr_flag = True
        else:
            same_data_attr_flag = False

        # Read the input data file and load all the record values to a list
        #
        print("encode_data_set_name:", encode_data_set_name)
        print("encode_rec_id_col:", encode_rec_id_col)
        print("encode_attr_list:", encode_attr_list)
        print("encode_col_sep_char:", encode_col_sep_char)
        print("encode_header_line_flag:", encode_header_line_flag)

        encode_rec_val_res_tuple = \
            importing.load_data_set_extract_attr_val(encode_data_set_name,
                                                     encode_rec_id_col,
                                                     encode_attr_list,
                                                     encode_col_sep_char,
                                                     encode_header_line_flag)
        print("pass encode 1 func")
        encode_rec_val_list = encode_rec_val_res_tuple[0]
        encode_rec_val_dict = encode_rec_val_res_tuple[1]
        encode_rec_val_id_dict = encode_rec_val_res_tuple[2]
        encode_rec_val_freq_dict = encode_rec_val_res_tuple[3]
        encode_attr_name_list = encode_rec_val_res_tuple[4]

        if (same_data_attr_flag == False):

            plain_rec_val_res_tuple = \
                importing.load_data_set_extract_attr_val(plain_data_set_name,
                                                         plain_rec_id_col,
                                                         plain_attr_list,
                                                         plain_col_sep_char,
                                                         plain_header_line_flag)

            plain_rec_val_list = plain_rec_val_res_tuple[0]
            plain_rec_val_dict = plain_rec_val_res_tuple[1]
            plain_rec_val_id_dict = plain_rec_val_res_tuple[2]
            plain_rec_val_freq_dict = plain_rec_val_res_tuple[3]
            plain_attr_name_list = plain_rec_val_res_tuple[4]
        else:
            plain_rec_val_list = encode_rec_val_list
            plain_rec_val_dict = encode_rec_val_dict
            plain_rec_val_id_dict = encode_rec_val_id_dict
            plain_rec_val_freq_dict = encode_rec_val_freq_dict
            plain_attr_name_list = encode_attr_name_list
        print("pass encode 2 func")

        # -----------------------------------------------------------------------------
        # Step 2: Generate Bloom filters for records
        #

        if (num_hash_funct == 'opt'):
            # Get average number of q-grams per record
            #
            enc_avrg_num_q_gram = importing.get_avrg_num_q_grams(encode_rec_val_list,
                                                                 encode_attr_list, q, padded)

            # Set number of hash functions to have in average 50% of bits set to 1
            # (reference to published paper? Only in Dinusha's submitted papers)
            # num_hash_funct = int(math.ceil(0.5 * BF_LEN / \
            #                                math.floor(avrg_num_q_gram)))
            #
            num_hash_funct = int(round(numpy.log(2.0) * float(bf_len) /
                                       enc_avrg_num_q_gram))
        print("pass encode 3 func")
        enc_param_list = []

        encode_bf_dict, encode_true_q_gram_pos_map_dict = \
            bfEncoding.gen_bloom_filter_dict(encode_rec_val_list, encode_rec_id_col,
                                             bf_encode, hash_type, bf_len,
                                             num_hash_funct, encode_attr_list, q,
                                             padded, bf_harden, enc_param_list,
                                             harden_param_list)
        pm_dict['q'] = q
        pm_dict['padded'] = padded
        pm_dict['bf_harden'] = bf_harden
        pm_dict['encode_attr_list'] = encode_attr_list
        pm_dict['plain_attr_list'] = plain_attr_list
        pm_dict['plain_rec_id_col'] = plain_rec_id_col
        pm_dict['same_data_attr_flag'] = same_data_attr_flag
        pm_dict['encode_bf_dict'] = encode_bf_dict
        pm_dict['bf_encode'] = bf_encode
        pm_dict['hash_type'] = hash_type
        pm_dict['bf_len'] = bf_len
        pm_dict['num_hash_funct'] = num_hash_funct
        pm_dict['enc_param_list'] = enc_param_list
        pm_dict['res_file_name'] = res_file_name
        pm_dict['harden_param_list'] = harden_param_list
        pm_dict['encode_true_q_gram_pos_map_dict'] = encode_true_q_gram_pos_map_dict
        pm_dict['encode_base_data_set_name'] = encode_base_data_set_name
        pm_dict['plain_base_data_set_name'] = plain_base_data_set_name
        pm_dict['mc_chain_len'] = mc_chain_len
        pm_dict['mc_sel_method'] = mc_sel_method
        pm_dict['encode_rec_id_col'] = encode_rec_id_col
        pm_dict['encode_rec_val_list'] = encode_rec_val_list
        pm_dict['encode_attr_name_list'] = encode_attr_name_list
        pm_dict['plain_rec_val_list'] = plain_rec_val_list
        pm_dict['plain_attr_name_list'] = plain_attr_name_list
        pm_dict['encode_rec_val_res_tuple'] = (encode_rec_val_list, encode_rec_val_dict, encode_rec_val_id_dict,
                                                    encode_rec_val_freq_dict, encode_attr_name_list)
        pm_dict['plain_rec_val_res_tuple'] = (plain_rec_val_list, plain_rec_val_dict, plain_rec_val_id_dict,
                                                    plain_rec_val_freq_dict, plain_attr_name_list)

        QMessageBox.information(self, 'message', "encode successfully")
        self.encoded_check(encode_bf_dict)

    def attack_pm(self, ini_start_time, pattern_mine_method_list, stop_iter_perc,
               stop_iter_perc_lm, min_part_size, max_num_many, re_id_method, expand_lang_model, lang_model_min_freq):
        global pm_dict
        global result_name_list
        #
        for pattern_mine_method in pattern_mine_method_list:
            assert pattern_mine_method in ['apriori', 'mapriori', 'maxminer', \
                                           'hmine', 'fpmax']

        #
        stop_iter_perc = float(stop_iter_perc)
        assert 0.0 < stop_iter_perc < 100.0, stop_iter_perc
        stop_iter_perc_lm = float(stop_iter_perc_lm)
        assert 0.0 < stop_iter_perc_lm < 100.0, stop_iter_perc_lm
        min_part_size = float(min_part_size)
        assert min_part_size > 1, min_part_size
        max_num_many = float(max_num_many)
        assert max_num_many > 1, max_num_many
        assert re_id_method in ['all', 'set_inter', 'bf_tuple', 'none']
        assert expand_lang_model in ['single', 'tuple', 'all'], expand_lang_model
        lang_model_min_freq = float(lang_model_min_freq)
        assert lang_model_min_freq >= 1, lang_model_min_freq
        self.pgb.setValue(5)
        pma.attack(pm_dict['q'], pm_dict['padded'], pm_dict['bf_harden'], pm_dict['encode_attr_list'], pm_dict['plain_attr_list'], pm_dict['plain_rec_id_col'], pm_dict['same_data_attr_flag'],
                   pm_dict['encode_bf_dict'], pm_dict['bf_encode'], pm_dict['hash_type'], pm_dict['bf_len'], pm_dict['num_hash_funct'], pm_dict['enc_param_list'], pm_dict['res_file_name'],
                   ini_start_time,
                   pm_dict['harden_param_list'], pm_dict['encode_true_q_gram_pos_map_dict'], pattern_mine_method_list,
                   pm_dict['encode_base_data_set_name'],
                   pm_dict['plain_base_data_set_name'], pm_dict['mc_chain_len'], pm_dict['mc_sel_method'], pm_dict['encode_rec_id_col'], pm_dict['encode_rec_val_list'],
                   pm_dict['encode_attr_name_list'], pm_dict['plain_rec_val_list'], pm_dict['plain_attr_name_list'],
                   str(pattern_mine_method_list), stop_iter_perc, stop_iter_perc_lm, min_part_size,
                   max_num_many, re_id_method, expand_lang_model, lang_model_min_freq,
                   self.pgb)
        self.pgb.setValue(100)
        QMessageBox.information(self, 'message', "attack finished!")

        result_name_list.append(pm_dict['res_file_name'])
        self.setRightWidget(flag=C.FLAG_EVAL)

    def attack_bpf(self, ini_start_time, min_freq, num_freq_attr_val_list):
        global pm_dict
        global result_name_list
        #
        num_freq_attr_val_list = list(num_freq_attr_val_list[1:-1].split(','))
        num_freq_attr_val_list = list(map(int, num_freq_attr_val_list))
        #
        min_freq = int(min_freq)
        assert min_freq >= 1, min_freq
        self.pgb.setValue(5)
        success = bpf.attack(pm_dict['q'], pm_dict['padded'], pm_dict['bf_harden'], pm_dict['encode_bf_dict'], pm_dict['bf_encode'], pm_dict['hash_type'],
                   pm_dict['bf_len'], pm_dict['num_hash_funct'], pm_dict['res_file_name'],
                   pm_dict['encode_base_data_set_name'], pm_dict['plain_base_data_set_name'], pm_dict['encode_rec_val_res_tuple'],
                   pm_dict['plain_rec_val_res_tuple'], min_freq, num_freq_attr_val_list,
                   self.pgb)
        self.pgb.setValue(100)
        if success == "fine":
            QMessageBox.information(self, 'message', "Attack finished!")
            result_name_list.append(pm_dict['res_file_name'])
        else:
            QMessageBox.information(self, 'message', "    Attack Failed\n"
                                                     "ERROR: most frequent BF's frequency\n"
                                                     "is not higher than 1. Details are in the Error_log\n"
                                                     "Please try again with new setting.")

            result_name_list.append(success)
        self.setRightWidget(flag=C.FLAG_EVAL)

    def getResultList(self, name):
        global result_name_list

        data = pd.read_csv(name)
        if len(data) == 0:
            self.tableWidget.setRowCount(1)
            item = QTableWidgetItem()
            item.setTextAlignment(QtCore.Qt.AlignCenter)
            item.setText("No data")
            self.tableWidget.setItem(0, 0, item)
            return

        self.tableWidget.setRowCount(data.shape[0] + 1)
        self.tableWidget.setColumnCount(data.shape[1])

        # table column name
        _translate = QtCore.QCoreApplication.translate
        column_name_list = list(data.columns)
        for i in range(len(column_name_list)):
            item = QtWidgets.QTableWidgetItem()
            self.tableWidget.setHorizontalHeaderItem(i, item)
        self.verticalLayout.addWidget(self.tableWidget)
        for i in range(len(column_name_list)):
            item = self.tableWidget.horizontalHeaderItem(i)
            item.setText(_translate("Form", column_name_list[i]))

        for i in range(data.shape[0]):
            for j in range(data.shape[1]):
                item = QTableWidgetItem(str(data.iloc[i, j]))
                item.setTextAlignment(QtCore.Qt.AlignCenter)
                item.setFlags(QtCore.Qt.ItemIsEnabled)
                self.tableWidget.setItem(i + 1, j, item)


def main():
    app = QtWidgets.QApplication(sys.argv)
    gui = MainUi()
    gui.show()
    sys.exit(app.exec_())


if __name__ == '__main__':
    main()
