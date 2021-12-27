/* eslint-disable jsx-a11y/no-static-element-interactions */
import React, {
  useState, useCallback, useRef, useEffect,
} from 'react';
import { makeStyles } from '@material-ui/core/styles';
import Typography from '@material-ui/core/Typography';
import ExpandMoreIcon from '@material-ui/icons/ExpandMore';
import Tooltip from '@material-ui/core/Tooltip';
import { MultipleChoiceSection, MultipleChoice } from './MultipleSectionItem';
import MultipleSelectorPopup, { SearchTextFieldProps, SearchTextFieldInputProps } from './MultipleSelectorPopup';

const useStyles = makeStyles({
  selectDiv: {
    alignItems: 'center',
    flex: 1,
    display: 'flex',
    border: '1px solid #E6E6E6',
    borderRadius: '4px',
    width: '170px',
    height: '35px',
    position: 'relative',
    padding: '0px 15px',
    '&:hover': {
      border: '1px solid #919191 !important',
    },
    backgroundColor: 'white',
    outline: 'none !important',
    outlineOffset: 'none !important',
  },
  disabled: {
    pointerEvents: 'none',
    background: '#E6E6E6',
    border: '1px solid #424242 important',
    '& svg': {
      color: '#828282',
    },
    '& p': {
      opacity: 0.35,
    },
  },
  openSelect: {
    border: '1px solid #919191 !important',
  },
  textContainer: {
    width: '100%',
    display: 'flex',
    overflow: 'hidden',
  },
  label: {
    display: 'flex',
    maxWidth: '100%',
    minWidth: '100%',
    width: '0px',
  },
  expandIcon: {
    display: 'flex',
    padding: '1px',
    right: '0',
    marginLeft: 'auto',
  },
  errorDiv: {
    border: '1px solid #D64646 !important',
  },
  groupTag: {
    color: '#63B178',
    whiteSpace: 'pre',
    fontStyle: 'italic',
  },
  placeholder: {
    whiteSpace: 'nowrap',
    color: '#919191',
    opacity: 0.75,
    fontStyle: 'italic',
    fontWeight: 400,
    overflow: 'hidden',
  },
});

export interface MultipleSelectorProps {
  label: string;
  popUpKey: string;
  choiceSections: MultipleChoiceSection[];
  name?: string;
  error?: boolean;
  placeholder?: string;
  disable?:boolean;
  checkedChoices?: MultipleChoice[];
  id?: string;
  style?: React.CSSProperties;
  className?: string,
  selectDivPropsStyle?: React.CSSProperties;
  selectDivClassName?: string;
  itemHeight?: number;
  scrollDivHeight?: number;
  popupClassName?: string;
  itemClassName?: string;
  sectionNameClassName?: string;
  disableDropDownArrow?: boolean;
  dropDownArrowClassName?: string;
  dropDownArrowComponent?: HTMLElement;
  searchTextFieldProps?: SearchTextFieldProps;
  searchTextFieldInputProps?: SearchTextFieldInputProps;
  handleSelect: ({ value, name }: { value: MultipleChoice[], name: string }) => void;
}

export const MultipleSelector: React.FC<MultipleSelectorProps> = ({
  label,
  name,
  popUpKey,
  error,
  choiceSections,
  placeholder,
  disable,
  checkedChoices,
  id,
  className,
  style,
  selectDivPropsStyle,
  selectDivClassName,
  itemHeight,
  scrollDivHeight,
  popupClassName,
  itemClassName,
  sectionNameClassName,
  disableDropDownArrow,
  dropDownArrowClassName,
  searchTextFieldProps,
  dropDownArrowComponent,
  searchTextFieldInputProps,
  handleSelect,
}) => {
  const classes = useStyles();
  const [open, setOpen] = useState<boolean>(false);
  const [chosenChoice, setChosenChoice] = useState<{[key: string]: MultipleChoice | null}>({});
  const [mulChoiceSections, setMulChoiceSections] = useState<MultipleChoiceSection[]>([...choiceSections]);
  const selectFieldRef = useRef<HTMLDivElement>(null);

  const handleClosePopup = useCallback((submitChoices: {[key: string]: MultipleChoice | null}) => {
    setOpen(false);
    if (submitChoices) {
      let selectedChoice = Object.keys(submitChoices).reduce((acc, choiceLabel) => {
        const choice = submitChoices[choiceLabel];
        return (
          choice ? [...acc, choice] : acc
        )
      }, [])
      // handle if previously user select single choice
      // and user not selecting new choices
      if (Object.keys(submitChoices).length === 0
        && checkedChoices
        && checkedChoices[0]
        && checkedChoices[0].singleChoice) {
        selectedChoice = [checkedChoices[0]];
      }
      handleSelect({ value: selectedChoice, name: name ?? '' });
    }
  }, [checkedChoices, handleSelect, name]);

  const handleSelectChoice = (value: MultipleChoice, isCheck: boolean) => {
    setChosenChoice({ ...chosenChoice, [`${value.id ?? value.label}`]: (isCheck || value.singleChoice) ? value : null });
    if (value.singleChoice) {
      handleClosePopup({ [`${value.singleChoice ? 'Single -' : ''}${value.id ?? value.label}`]: (isCheck || value.singleChoice) ? value : null });
    }
  };

  const handleClearAll = () => {
    setChosenChoice({});
  };

  useEffect(() => {
    const initChosenChoice: { [key: string]: MultipleChoice } = {};
    if (checkedChoices && checkedChoices[0] && !checkedChoices[0].singleChoice) {
      checkedChoices.forEach((choice) => {
        if (choice.label.trim().length > 0) {
          initChosenChoice[`${choice.singleChoice ? 'Single -' : ''}${choice.id ?? choice.label}`] = choice;
        }
      });
    }
    setChosenChoice(initChosenChoice);
    setMulChoiceSections(choiceSections.map((section) => ({
      ...section, choices: section.choices.map((choice) => ({ ...choice, checked: Boolean(initChosenChoice[`${choice.singleChoice ? 'Single -' : ''}${choice.id ?? choice.label}`]) })),
    })));
  }, [checkedChoices, choiceSections]);

  return (
    <div ref={selectFieldRef} style={{ width: '100%', display: 'flex', ...style }} className={className}>
      <Tooltip
        title={checkedChoices ? checkedChoices?.map((choice) => choice.label).join(', ') : ''}
        placement="top"
        arrow
      >
        <button
          type="button"
          className={`
          ${classes.selectDiv}
          ${open ? classes.openSelect : ''}
          ${error ? classes.errorDiv : ''}
          ${disable ? classes.disabled : ''}
          ${selectDivClassName}
        `}
          style={selectDivPropsStyle}
          onClick={() => setOpen(true)}
          id={`${id}-multiple-selector-button`}
        >
          {!disable && (
          <div className={classes.textContainer}>
            {(label === undefined || label.length === 0)
              ? (
                <Typography variant="body1" className={classes.placeholder}>
                  {placeholder}
                </Typography>
              )
              : (
                <Typography variant="body1" className={classes.label} noWrap>
                  {label}
                </Typography>
              )}
          </div>
          )}
          {!disableDropDownArrow && <div className={`${classes.expandIcon} ${dropDownArrowClassName}`}>
            {dropDownArrowComponent || <ExpandMoreIcon style={{ fontSize: '15px' }} />}
          </div>}
        </button>
      </Tooltip>
      {open && selectFieldRef.current &&  (
        <MultipleSelectorPopup
          choiceSections={mulChoiceSections}
          anchorEl={selectFieldRef.current}
          popUpKey={popUpKey}
          name={name ?? ''}
          chosenChoice={chosenChoice}
          id={id}
          itemHeight={itemHeight}
          scrollDivHeight={scrollDivHeight}
          handleSelect={handleSelectChoice}
          handleClose={handleClosePopup}
          handleClearAll={handleClearAll}
          className={popupClassName}
          itemClassName={itemClassName}
          sectionNameClassName={sectionNameClassName}
          searchTextFieldProps={searchTextFieldProps}
          searchTextFieldInputProps={searchTextFieldInputProps}
        />
      )}
    </div>
  );
};

export type { MultipleChoiceSection, MultipleChoice, SearchTextFieldProps, SearchTextFieldInputProps };
